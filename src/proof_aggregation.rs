use plonky2::{
    iop::witness::{PartialWitness, WitnessWrite},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::CircuitData,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};

use crate::{utilities::RefOrValue, BaseField, PGConfig, D};

/// Given `repeat_circuit``, outputs another circuit
/// that takes `how_many` proofs of instances of the `repeat_circuit`
/// and produces an aggregated proof that the input proofs are valid.
///
/// Optionally, a second circuit input can be provided to be aggregated once,
/// after the first one has been inserted `how_many` times.
///
/// The output circuit exposes all the public inputs of the proofs
/// that are being aggregated. This makes the verification process slower
/// but allows external entities to easily retrieve information from the
/// public inputs of the individual proofs.
///
/// If `proof_targets.is_some()`, the function will append the information on
/// the proof targets in the newly formed circuit to `proof_targets`.
///
/// The return value is the output circuit, together with the targets one
/// should use to build the partial witness to feed to the prover of the
/// output circuit.
fn helper_aggregate_and_forward_public_input(
    repeat_circuit: &CircuitData<BaseField, PGConfig, D>,
    how_many: usize,
    remainder: Option<&CircuitData<BaseField, PGConfig, D>>,
    mut proof_targets: Option<&mut Vec<ProofWithPublicInputsTarget<D>>>,
) -> CircuitData<BaseField, PGConfig, D> {
    let mut builder = CircuitBuilder::new(repeat_circuit.common.config.clone());
    let inner_verifier_data = builder.constant_verifier_data(&repeat_circuit.verifier_only);

    for _ in 0..how_many {
        let proof_with_pis = builder.add_virtual_proof_with_pis(&repeat_circuit.common);
        builder.verify_proof::<PGConfig>(
            &proof_with_pis,
            &inner_verifier_data,
            &repeat_circuit.common,
        );
        builder.register_public_inputs(&proof_with_pis.public_inputs);

        if let Some(ref mut proof_targets) = proof_targets {
            proof_targets.push(proof_with_pis);
        }
    }

    if let Some(remainder) = remainder {
        let inner_verifier_data = builder.constant_verifier_data(&remainder.verifier_only);

        let proof_with_pis = builder.add_virtual_proof_with_pis(&remainder.common);
        builder.verify_proof::<PGConfig>(&proof_with_pis, &inner_verifier_data, &remainder.common);
        builder.register_public_inputs(&proof_with_pis.public_inputs);

        if let Some(proof_targets) = proof_targets {
            proof_targets.push(proof_with_pis);
        }
    }

    builder.build()
}

/// Given the description of a circuit, outputs another circuit
/// that takes `how_many` proofs of instances of the input circuit
/// and produces an aggregated proof that the input proofs are valid.
///
/// The output circuit exposes all the public inputs of the proofs
/// that are being aggregated. This makes the verification process slower
/// but allows external entities to easily retrieve information from the
/// public inputs of the individual proofs.
///
/// `max_group_size` determines how the proofs are aggregated. Since aggregating
/// all of them at once would require a lot of memory on the machine being used,
/// one has to adopt a recursive approach, like the one used in a Merkle tree.
///
/// Given a proof for the output circuit, one can deserialize the public
/// inputs of the instances if the input circuit by using
/// `deserialize_aggregated_proof_public_input`
pub fn circuit_aggregate_proofs_forward_input(
    circuit: &CircuitData<BaseField, PGConfig, D>,
    mut how_many: usize,
    max_group_size: usize,
) -> CircuitData<BaseField, PGConfig, D> {
    assert!(
        max_group_size > 1,
        "A `max_group_size` of at least 2 is required."
    );
    assert!(
        how_many > 1,
        "Aggregating only one copy of a circuit does not make sense."
    );

    let mut full_agg_circuit = RefOrValue::Ref(circuit);
    let mut remainder_circuit = None;

    loop {
        if how_many < max_group_size {
            if how_many == 1 && remainder_circuit.is_none() {
                return match full_agg_circuit {
                    RefOrValue::Value(v) => v,
                    _ => unreachable!(
                        "                       the initial value of `how_many` is not 1. So,
                        - if initially `how_many >= max_group_size`, then
                          `full_agg_circuit` was set to Value at the end of
                          the first loop iteration.
                        - otherwise if initially `2 <= how_many < max_group_size`,
                          then the return soon after this if clause is executed."
                    ),
                };
            }
            return helper_aggregate_and_forward_public_input(
                &*full_agg_circuit,
                how_many,
                remainder_circuit.as_ref(),
                None,
            );
        }

        if how_many % max_group_size != 0 {
            remainder_circuit = Some(helper_aggregate_and_forward_public_input(
                &*full_agg_circuit,
                how_many % max_group_size,
                remainder_circuit.as_ref(),
                None,
            ));
        }

        full_agg_circuit = RefOrValue::Value(helper_aggregate_and_forward_public_input(
            &*full_agg_circuit,
            max_group_size,
            None,
            None,
        ));

        how_many /= max_group_size;
    }
}

impl<'a, T> std::ops::Deref for RefOrValue<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Ref(r) => r,
            Self::Value(v) => v,
        }
    }
}

pub fn aggregate_proofs(
    circuit: &CircuitData<BaseField, PGConfig, D>,
    proofs: Vec<ProofWithPublicInputs<BaseField, PGConfig, D>>,
    max_group_size: usize,
) -> Result<ProofWithPublicInputs<BaseField, PGConfig, D>, ()> {
    let how_many = proofs.len();
    assert!(how_many > 1, "cannot aggregate less than 2 proofs");

    let mut repeat_circuit = RefOrValue::Ref(circuit);
    let mut repeat_proof_targets = vec![];

    let mut remainder_circuit = None;
    let mut remainder_proof_targets = vec![];
    let mut remainder_proof = None;

    let mut read_proof_buffer = proofs;
    let mut write_proof_buffer = vec![];

    let mut full_agg_circuit;

    // This loop will continue until
    //
    // ```
    // (
    //     write_proof_buffer.is_empty() &&
    //     remainder_proof.is_some()
    // ) || (
    //     write_proof_buffer.len() == 1 &&
    //     remainder_proof.is_none()
    // )
    // ```
    //
    // this condition will be reached at some point, because at every new
    // iteration, `write_proof_buffer` and `read_proof_buffer` are swapped,
    // `write_proof_buffer` will be cleared, and it will be filled with
    // `read_proof_buffer.len() / max_group_size` items,
    // and as for `remainder_proof`, if at any point
    // `read_proof_buffer.len() & max_group_size != 0`,
    // then `remainder_proof` will be set to `Some(..)`, and once it is
    // `Some(..)`, it cannot go back to `None`.
    loop {
        repeat_proof_targets.clear();
        full_agg_circuit = helper_aggregate_and_forward_public_input(
            &*repeat_circuit,
            max_group_size,
            None,
            Some(&mut repeat_proof_targets),
        );

        let mut proofs = read_proof_buffer.as_slice();

        // We fill `write_proof_buffer` with proofs that aggregate `max_group_size`
        // repetitions of `repeat_circuit` proofs.
        while proofs.len() >= max_group_size {
            let (proof_batch, others) = proofs.split_at(max_group_size);
            proofs = others;

            let mut witness = PartialWitness::new();
            for (target, proof) in repeat_proof_targets.iter().zip(proof_batch) {
                witness.set_proof_with_pis_target(target, proof);
            }
            write_proof_buffer.push(full_agg_circuit.prove(witness).map_err(|_| ())?);
        }

        // in case there are some left, we aggregate them separately in
        // `remainder_proof`. If `remainder_proof.is_some()`, we include it
        // in the aggregation process.
        if proofs.len() > 0 {
            remainder_proof_targets.clear();
            remainder_circuit = Some(helper_aggregate_and_forward_public_input(
                &*repeat_circuit,
                proofs.len(),
                remainder_circuit.as_ref(),
                Some(&mut remainder_proof_targets),
            ));
            let mut witness = PartialWitness::new();
            for (idx, proof) in proofs.into_iter().enumerate() {
                let target = &remainder_proof_targets[idx];
                witness.set_proof_with_pis_target(target, proof);
            }
            if let Some(ref mut remainder_proof) = remainder_proof {
                let target = &remainder_proof_targets[proofs.len()];
                witness.set_proof_with_pis_target(target, remainder_proof);
            }

            remainder_proof = Some(
                remainder_circuit
                    .as_ref()
                    .expect("we just set `remainder_circuit` to Some(..)")
                    .prove(witness)
                    .map_err(|_| ())?,
            );

            // If the buffer is empty, that means that in next loop nothing
            // would be left to aggregate, so we are done, and the final
            // aggregated proof is `remainder_proof`.
            if write_proof_buffer.is_empty() {
                return remainder_proof.ok_or(());
            }
        } else {
            // If there is only one item in the write buffer, and no remainder proof,
            // then we are done, because in the next loop iteration we would have
            // no proofs to aggregate.
            if remainder_proof.is_none() && write_proof_buffer.len() == 1 {
                return Ok(write_proof_buffer
                    .pop()
                    .expect("we just checked that len == 1"));
            }
        }

        // We setup the variables for the next loop iteration.
        // We swap the read and write buffers, and we will use
        // `full_agg_circuit` as the next `repeat_circuit`.
        read_proof_buffer.clear();
        (read_proof_buffer, write_proof_buffer) = (write_proof_buffer, read_proof_buffer);
        repeat_circuit = RefOrValue::Value(full_agg_circuit);
    }
}

pub fn deserialize_aggregated_proof_public_input(
    inner_circuit: &CircuitData<BaseField, PGConfig, D>,
    how_many: usize,
    aggregated_proof: &ProofWithPublicInputs<BaseField, PGConfig, D>,
) -> Result<Vec<Vec<BaseField>>, (usize, usize, usize, usize)> {
    let inner_proof_public_input_len = inner_circuit.common.num_public_inputs;
    if aggregated_proof.public_inputs.len() != how_many * inner_proof_public_input_len {
        return Err((
            aggregated_proof.public_inputs.len(),
            how_many * inner_proof_public_input_len,
            how_many,
            inner_proof_public_input_len,
        ));
    }
    Ok(Vec::from_iter(
        aggregated_proof
            .public_inputs
            .chunks(inner_proof_public_input_len)
            .map(|chunk| chunk.into()),
    ))
}
