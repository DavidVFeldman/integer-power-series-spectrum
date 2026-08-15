import SpectrumFormalization.UltraTrace
import SpectrumFormalization.PadicEval

/-!
# Axiom audit of the Tier A–D headline declarations

Each `#print axioms` below must report exactly
`propext, Classical.choice, Quot.sound`.
-/

namespace RequestProject

-- Tier A
#print axioms exists_RRsub_realization_order
#print axioms ODorder_mul
#print axioms ODevalAt_eq_zero_iff_ODorder_pos
#print axioms ODorder_zero_of_ev0RR_eq_one

-- Tier B
#print axioms partition_property

-- Tier C
#print axioms exists_realizer
#print axioms mem_ultraPrime_iff_zeroSet
#print axioms exists_generator_of_mem
#print axioms ultraPrime_isInP1
#print axioms ultraPrime_injective

-- Tier D
#print axioms psiP
#print axioms Qp_isPrime
#print axioms zElt_add_p_mem
#print axioms Qp_ne_bot
#print axioms zElt_not_mem_Qp
#print axioms intCast_mem_Qp_iff
#print axioms psiP_mod_p
#print axioms Qp_not_isInP1
#print axioms primes_outside_classification_false
#print axioms psiP_surjective
#print axioms quotQpEquiv
#print axioms Qp_not_isMaximal

end RequestProject
