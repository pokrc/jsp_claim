import JspClaim.JSP000301_StatementBridge
import JspClaim.JSP000689_Exponential
import JspClaim.JSP000900_DistanceProfiles
import JspClaim.JSP000900_OneDimensional
import JspClaim.JSP000900_ConditionalRate

/-!
A pinned, CI-runnable axiom and theorem-scope report.
Run: lake env lean ProofAudit.lean
The original selected proof commits remain unchanged.
This is not an automatic award-eligibility or originality certification.
-/

#check JSP000301.jsp000301
#check JSP000301.positive_counterexample
#check JSP000301.published_question_false
#check JSP000689.erdos_lovasz_explicit_finite
#check JSP000689.erdos_lovasz_exponential_finite
#print axioms JSP000301.jsp000301
#print axioms JSP000301.published_question_false
#print axioms JSP000689.erdos_lovasz_explicit_finite
#print axioms JSP000689.erdos_lovasz_exponential_finite

/-!
JSP-000900 research: the main theorem is UNPROVED.
Check only completed, correctly scoped supporting lemmas; the final line
checks the type of the still-unproved conjecture.
-/
#check JSP000900.OriginalQuestion
#check JSP000900.distanceValues_nonneg
#check JSP000900.distanceValues_mono
#check JSP000900.distanceValues_card_mono
#check JSP000900.zero_not_mem_distanceValues
#check JSP000900.card_sub_one_le_distanceValues_of_radial_inj
#check JSP000900.one_le_distanceValues_card_of_two_points
#check JSP000900.real_distinct_distances_lower_bound
#check JSP000900.high_dimensional_bound_of_radial_inj
#check JSP000900.card_le_distance_spectrum_pow_of_injective_profile

#print axioms JSP000900.distanceValues_nonneg
#print axioms JSP000900.distanceValues_mono
#print axioms JSP000900.distanceValues_card_mono
#print axioms JSP000900.zero_not_mem_distanceValues
#print axioms JSP000900.card_sub_one_le_distanceValues_of_radial_inj
#print axioms JSP000900.one_le_distanceValues_card_of_two_points
#print axioms JSP000900.real_distinct_distances_lower_bound
#print axioms JSP000900.high_dimensional_bound_of_radial_inj
#print axioms JSP000900.card_le_distance_spectrum_pow_of_injective_profile
