module

import ErdosProofs.Erdos881.K2

/-!
# Axiom check for Problem 881

Building this module prints the axioms that each theorem in `K2.lean` depends on. Each should
list only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms Erdos881K2.infinite_deletion_of_two_basis
#print axioms Erdos881K2.erdos_881_two
#print axioms Erdos881K2.not_minimal_three_of_two_basis
