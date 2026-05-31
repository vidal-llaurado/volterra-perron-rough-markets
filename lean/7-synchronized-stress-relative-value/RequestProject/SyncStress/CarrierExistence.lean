/-
# Proposition 5.4: Existence of carrier weights

If Δ is nonempty, compact, and convex, then the squared-Euclidean projection
onto Δ exists and is unique.

From: "Synchronized Stress Relative Value" by J. Vidal Llauradó (2026).
-/
import Mathlib

open scoped BigOperators

noncomputable section

/-! ## Proposition 5.4 (Existence of carrier weights)

The carrier basket is the projection of the unconstrained weight vector onto a
compact convex feasible set in squared Euclidean distance. Existence follows from
the Weierstrass extreme value theorem; uniqueness follows from strict convexity
of the squared distance. -/

/-
**Proposition 5.4 (Existence).** A continuous function on a nonempty compact set
    attains its infimum. Applied here: the squared Euclidean distance from a target
    point to a nonempty compact set has a minimizer.
-/
theorem carrier_existence {n : ℕ}
    (Delta : Set (EuclideanSpace ℝ (Fin n)))
    (hne : Delta.Nonempty) (hcpt : IsCompact Delta)
    (b_bar : EuclideanSpace ℝ (Fin n)) :
    ∃ b ∈ Delta, ∀ b' ∈ Delta, dist b b_bar ≤ dist b' b_bar := by
  exact ( hcpt.exists_isMinOn hne ( Continuous.continuousOn ( continuous_id.dist continuous_const ) ) )

/-
**Proposition 5.4 (Uniqueness).** The nearest-point projection onto a convex set
    in a strictly convex normed space is unique.
-/
theorem carrier_uniqueness {n : ℕ}
    (Delta : Set (EuclideanSpace ℝ (Fin n)))
    (hne : Delta.Nonempty) (hcpt : IsCompact Delta) (hcvx : Convex ℝ Delta)
    (b_bar : EuclideanSpace ℝ (Fin n))
    (b₁ b₂ : EuclideanSpace ℝ (Fin n))
    (hb₁ : b₁ ∈ Delta) (hb₂ : b₂ ∈ Delta)
    (h₁ : ∀ b' ∈ Delta, dist b₁ b_bar ≤ dist b' b_bar)
    (h₂ : ∀ b' ∈ Delta, dist b₂ b_bar ≤ dist b' b_bar) :
    b₁ = b₂ := by
  -- By definition of absolute value, we know that for any $x$, $|x| \leq y$ if and only if $-y \leq x \leq y$.
  by_contra h_neq;
  -- By the properties of the Euclidean norm, we know that $‖b₁ - b_bar‖ = ‖b₂ - b_bar‖$.
  have h_norm_eq : ‖b₁ - b_bar‖ = ‖b₂ - b_bar‖ := by
    exact le_antisymm ( by simpa [ dist_eq_norm ] using h₁ b₂ hb₂ ) ( by simpa [ dist_eq_norm ] using h₂ b₁ hb₁ );
  -- By the properties of the Euclidean norm, we know that $‖b₁ - b_bar‖^2 + ‖b₂ - b_bar‖^2 = 2‖(b₁ + b₂)/2 - b_bar‖^2 + ‖b₁ - b₂‖^2 / 2$.
  have h_norm_sq_eq : ‖b₁ - b_bar‖^2 + ‖b₂ - b_bar‖^2 = 2 * ‖(1 / 2 : ℝ) • (b₁ + b₂) - b_bar‖^2 + ‖b₁ - b₂‖^2 / 2 := by
    norm_num [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
    norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_div, sub_sq ] ; ring;
    norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring;
    norm_num [ ← Finset.sum_mul _ _ _ ] ; ring;
  -- Since $b₁ \neq b₂$, we have $‖b₁ - b₂‖ > 0$.
  have h_norm_pos : ‖b₁ - b₂‖ > 0 := by
    exact norm_pos_iff.mpr ( sub_ne_zero.mpr h_neq );
  -- Since $b₁ \neq b₂$, we have $‖(1 / 2 : ℝ) • (b₁ + b₂) - b_bar‖ < ‖b₁ - b_bar‖$.
  have h_norm_lt : ‖(1 / 2 : ℝ) • (b₁ + b₂) - b_bar‖ < ‖b₁ - b_bar‖ := by
    nlinarith [ norm_nonneg ( b₁ - b_bar ), norm_nonneg ( b₂ - b_bar ), norm_nonneg ( b₁ - b₂ ) ];
  exact not_le_of_gt h_norm_lt ( by simpa [ dist_eq_norm ] using h₁ _ ( hcvx hb₁ hb₂ ( by norm_num ) ( by norm_num ) ( by norm_num ) ) )

end