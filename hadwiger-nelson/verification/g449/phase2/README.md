# G449 follow-up: reusable norm certificates and chunked edge data

This extends the two-edge calibration. It is not an independent replay of the authors' four-color refutation, and it does not improve the unrestricted 6–7 bounds.

DirectNorm.lean proves that the shifted Laurent double sum for exact cyclotomic coefficients is the complex norm-square and that a certificate for it makes a unit-distance edge in the actual Euclidean metric. Rotation42.lean checks the 12-coordinate integer map representing multiplication by ζ⁶ and proves its norm invariance. These generic theorems compiled under plain Lean 4.36.0, with only propext, Classical.choice, and Quot.sound.

The accompanying original generators use the locally obtained pinned publication artifacts described in the preceding G449 pilot; do not commit generated coordinate tables from those data. To reproduce the two successful data modules, place these sources and scripts alongside the prior pilot scripts after running the prior independent Python replay. Then run:

    python3 gen_direct.py 0 7 NormShard00.lean
    python3 gen_edges.py 0 60 EdgeShard0000.lean

Build in order: CyclotomicWitness, DirectNorm, Rotation42, G449BalancedData, NormShard00, EdgeShard0000. The directory must be on LEAN_PATH for local module imports if using direct lean invocations.

- NormShard00.lean: the first seven of the 49 extracted unoriented directions have the exact required norm; the quotient expansion is checked by Lean, not trusted from Python.
- EdgeShard0000.lean: the first 60 of the 2,198 input edges have their exact original endpoint coefficient differences equal to the indicated signed direction from the data table. Its certificate theorem uses only propext.
- These two claims do not assert 60 unit-distance theorems: they overlap in 21 edges. The original two-endpoint calibration remains independently checked.

The optional exact Python audit can be reproduced with python3 orbit_audit.py in the input directory. It identifies 1 fixed vertex and 64 seven-cycles on vertices, plus seven rotation orbits on the 49 directions and 314 rotation orbits on the 2,198 edges. The Lean geometric rotation invariance is in place, but the orbit-coverage and all-edge closure are not yet verified end to end in Lean.
