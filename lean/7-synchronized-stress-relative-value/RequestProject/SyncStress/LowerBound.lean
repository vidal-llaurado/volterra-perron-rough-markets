/-
# Proposition 6.2 & 6.4: Lower-bound certificate and sizing

From: "Synchronized Stress Relative Value" by J. Vidal Llauradó (2026).
-/
import Mathlib

noncomputable section

/-! ## Proposition 6.2 (Lower-bound positive-edge certificate)

If the conditional expected P&L satisfies `E[Y] ≥ LB` and `LB > 0`, then `E[Y] > 0`. -/

/-- **Proposition 6.2.** The lower-bound positive-edge certificate:
    if the forecast inequality `E[Y] ≥ LB` holds and `LB > 0`, then `E[Y] > 0`. -/
theorem lower_bound_certificate (EY LB : ℝ) (hforecast : EY ≥ LB) (hLB : LB > 0) :
    EY > 0 :=
  lt_of_lt_of_le hLB hforecast

/-! ## Proposition 6.4 (Lower-bound size as a capital decision)

The unconstrained lower-bound size maximizes `x * LB - (λ/2) * R * x²` over `x ≥ 0`.

When `LB > 0`, `λ > 0`, `R > 0`, the maximizer is `LB / (λ * R)`.
When `LB ≤ 0`, the maximizer is `0`. -/

/-- The one-dimensional quadratic capital objective. -/
def capitalObjective (LB lam R x : ℝ) : ℝ :=
  x * LB - (lam / 2) * R * x ^ 2

/-
**Proposition 6.4 (positive LB case).** When `LB > 0`, `λ > 0`, and `R > 0`,
    the maximizer of the capital objective over `x ≥ 0` is `LB / (λ * R)`.
-/
theorem lb_size_maximizer_pos (LB lam R : ℝ) (hLB : LB > 0) (hlam : lam > 0)
    (hR : R > 0) :
    ∀ x : ℝ, x ≥ 0 →
      capitalObjective LB lam R x ≤ capitalObjective LB lam R (LB / (lam * R)) := by
  intro x hx_nonneg; rw [ capitalObjective, capitalObjective ] ; ring_nf;
  field_simp;
  nlinarith [ sq_nonneg ( LB - x * lam * R ) ]

/-
**Proposition 6.4 (non-positive LB case).** When `LB ≤ 0`, `λ > 0`, and `R > 0`,
    the maximizer of the capital objective over `x ≥ 0` is `0`.
-/
theorem lb_size_maximizer_zero (LB lam R : ℝ) (hLB : LB ≤ 0) (hlam : lam > 0)
    (hR : R > 0) :
    ∀ x : ℝ, x ≥ 0 →
      capitalObjective LB lam R x ≤ capitalObjective LB lam R 0 := by
  exact fun x hx => by unfold capitalObjective; nlinarith [ mul_nonneg hlam.le ( mul_nonneg hR.le ( sq_nonneg x ) ) ] ;

end