module

import ErdosProofs.Erdos1139.Main

/-!
# Axiom check for Problem 1139

Building this module prints the axioms that each theorem in `Main.lean` depends on. Each should
list only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms Erdos1139Proof.erdos_1139
#print axioms Erdos1139Proof.erdos_1139_fc
