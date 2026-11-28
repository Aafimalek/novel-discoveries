# Four-isolate finite trace classifier: Lean certificate

**Scope: the finite trace classification only.** This folder does not
prove the full five-isolates theorem. The code contains no custom axiom,
placeholder, native decision, or external-oracle step. Exact outputs
are recorded in replay.log and the per-module logs.

The 11-bit family mask chooses the optional trace sets; the mandatory
set contains all five traces of size three or four. Each of the 16
possible individual traces is itself its 4-bit subset mask. Coordinate
0 is the strictly below-half isolate. The exact finite claims are:

- exactly 106 masks are eligible (union-closed and coordinate 0
  occurs strictly less than half);
- every eligible mask except 2045 has a witness consisting of
  a pair of isolated coordinates and four strictly nested containing
  traces, together with the verified safe-support and strict frequency
  inequality;
- mask 2045 is precisely the full trace cube except the distinguished
  singleton, is eligible, has frequencies 7/8/8/8 in 15 traces, and
  fails the strict frequency inequality at every coordinate pair.

Compile FranklFourTraceCertificateDefinitions.lean then
FranklFourTraceCertificates.lean on pinned Lean 4.36 with Mathlib.
The generator merely proposes a table of 105 witnesses. Lean
validates them against the definitions via ordinary kernel reduction,
together with all 2,048 masks, within 64
independent blocks of size 32. Internal append lemmas glue the blocks.
The Python generation is deterministic and is not imported as evidence.
Use `bash replay.sh` for the guarded one-worker replay. Set `LEAN_PATH` to the build libraries of pinned Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and its dependencies.

## Still-unformalized transfer to a weak Frankl family

1. **Labeled trace abstraction.** For exactly one source p and four
   isolates with a chosen below-half x, choose the four labels with
   x at 0. Prove membership of a coordinate and strict inclusions or
   union of finite isolate subsets correspond to the exposed Nat
   mask operations. Prove that every finite trace family containing
   the five mandatory sets is represented by some m<2048, with no
   multiplicity; the mask-existence proof requires no finite search.

2. **Encoding the source-containing fiber.** Use
   unique_source_all_nonisolates_present and
   exists_low_frequency_in_containing_fiber. Every set containing
   p is the fixed full star plus its isolate trace; thus trace
   projection is injective there, preserves cardinality and isolate
   frequencies, and preserves union closure. Use
   ground_mem_weak and isolated_coSingleton_mem to force the five
   mandatory traces. These facts give eligibleB m.

3. **Safe support and chain transfer.** For any source-avoiding set
   with isolate trace T, union it with each source-containing set.
   Every resulting isolate trace T union R is in the trace family,
   which is exactly the safe test. For a valid witness, each set
   avoiding the source and the selected two isolates has isolate
   support included in supportBits. Every such support is below the
   bottom of the four-member trace chain. Lift those four traces
   to four actual source-containing sets. Thus any strict
   three-chain in the avoiding family would extend to a forbidden
   seven-chain. Its ground has at most L+s points (L leaves and s
   safe-support bits). Apply the checked height-two size bound or
   the drafted general chain-extension wrapper to conclude size
   at most L+s+1.

4. **Strict incidence surplus.** The full source-avoiding top
   and L co-leaf maxima all contain the selected pair of isolates,
   using the checked avoid_mem_weak, notMem_avoid_iff_forces, and
   avoid_eq_coPair_of_edge. For the source-avoiding fiber B of
   cardinality b, partition original frequencies into B and the
   containing fiber P (frequency_partition_by_point). Summing weak
   half bounds for the pair gives
   f_B(i)+f_B(j)+f_P(i)+f_P(j) ≤ b+|P|. The number in B avoiding
   both is b−f_B(i)−f_B(j) plus the both count, which is at least
   L+1+f_P(i)+f_P(j)−|P|. The WitnessSpec surplus makes this
   strictly larger than L+s+1, a contradiction. Formalize the
   inequality without Nat-subtraction ambiguity.

5. **Survivor handoff.** Transport the survivor_profile counts
   to P and add that every non-isolate is in every P-set. Then
   invoke the already checked theorem
   FranklForcingFiber.no_containing_profile_fifteen_seven_eight.

Separately, the full at-least-five-isolates theorem still needs
the preexisting written multiple-source exact-four elimination
and the written exact-three elimination (or self-contained
formal substitutes). None is part of this numerical certificate.
