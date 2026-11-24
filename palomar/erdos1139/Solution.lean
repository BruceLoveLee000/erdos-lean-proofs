/-
Copyright 2026 Bruce Lee.
Released under the Apache License, Version 2.0.
-/
module

public import Erdos1139.Proof

/-!
# Erdős Problem 1139: proof

The proof development is in `Erdos1139/Proof.lean`, which proves `Erdos1139Proof.erdos_1139`
under the same name and statement as `Challenge.lean`.

Comparator checks that the compared declaration here has the same type as in `Challenge.lean`
and that the proof uses only `propext`, `Classical.choice` and `Quot.sound`.
-/
