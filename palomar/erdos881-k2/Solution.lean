/-
Copyright 2026 Bruce Lee.
Released under the Apache License, Version 2.0.
-/
module

public import Erdos881K2.Proof

/-!
# Erdős Problem 881 for `k = 2`: proofs

The proof development is in `Erdos881K2/Proof.lean`, which proves
`Erdos881K2.infinite_deletion_of_two_basis`, `Erdos881K2.erdos_881_two` and
`Erdos881K2.not_minimal_three_of_two_basis` under the same names
and statements as `Challenge.lean`. The definitions those statements use,
`Set.IsAsymptoticAddBasisOfOrder` and `Erdos881.IsMinimalAsymptoticAddBasisOfOrder`, are in
`Erdos881K2/Basis.lean`, copied from formal-conjectures.

Comparator checks that each compared declaration here has the same type as in `Challenge.lean`,
that the definitions they use agree, and that the proofs use only `propext`, `Classical.choice`
and `Quot.sound`.
-/
