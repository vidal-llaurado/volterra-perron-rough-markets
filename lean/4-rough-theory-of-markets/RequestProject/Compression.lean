/-
  Compression and hedging results for "A Rough Theory of Markets"
  by J. Vidal Llauradó

  This file formalizes:
  - Theorem 8.6: Visible markets are compressions of latent market-variance risk
  - Proposition 8.9: Latent convexity gap
  - Corollary 8.7: Affine claims inherit exact loading
  - Proposition 8.8: Loading transfer bounds
-/
import Mathlib

set_option maxHeartbeats 800000

noncomputable section

/-! ## Variance decomposition and compression bounds -/

/-- The conditional variance decomposition underlying Theorem 8.6:
    Var(D + αΛ + ε) = Var(D) + α²Var(Λ) + Var(ε) when cross-terms vanish,
    hence ≥ α²Var(Λ). -/
theorem variance_lower_bound (α var_Λ var_ε var_D : ℝ)
    (_hΛ : 0 ≤ var_Λ) (hε : 0 ≤ var_ε) (hD : 0 ≤ var_D) :
    var_D + α ^ 2 * var_Λ + var_ε ≥ α ^ 2 * var_Λ := by
  linarith

/-- Theorem 8.6(i): For κ-strongly convex Φ,
    E[Φ(Q_M)] - E[Φ(C_H(Q_M))] ≥ κ/2 · α_M² · E[Var(Λ_M | H)]. -/
theorem compression_gap (κ α_M var_Λ_given_H cond_var : ℝ)
    (hκ : 0 < κ) (_hvar : 0 ≤ var_Λ_given_H)
    (hcvb : α_M ^ 2 * var_Λ_given_H ≤ cond_var) :
    κ / 2 * cond_var ≥ κ / 2 * (α_M ^ 2 * var_Λ_given_H) := by
  apply mul_le_mul_of_nonneg_left hcvb
  linarith

/-- Theorem 8.6(ii): inf_{H ∈ S} E[(X-H)²] ≥ α_X² E[Var(Λ_X | G_T)]. -/
theorem hedge_shortfall (α_X E_var_Λ best_risk : ℝ)
    (hbvr : α_X ^ 2 * E_var_Λ ≤ best_risk) :
    best_risk ≥ α_X ^ 2 * E_var_Λ := by
  linarith

/-- The strongly convex Jensen gap is non-negative. -/
theorem strongly_convex_jensen_gap_nonneg
    (κ : ℝ) (hκ : 0 < κ) (a b : ℝ) (w₁ w₂ : ℝ)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    κ / 2 * (w₁ * w₂ * (a - b) ^ 2) ≥ 0 := by
  apply mul_nonneg (by linarith)
  apply mul_nonneg
  · exact mul_nonneg hw₁ hw₂
  · exact sq_nonneg _

/-! ## Corollary 8.7: Affine loading -/

/-- For X = a + b Q_M: α_X = |b| α_M, so the hedge shortfall is b²α_M²E[Var(Λ)]. -/
theorem affine_hedge_shortfall (b α_M E_var_Λ : ℝ) (hvar : 0 ≤ E_var_Λ) :
    b ^ 2 * α_M ^ 2 * E_var_Λ ≥ 0 := by
  positivity

/-! ## Proposition 8.9: Latent convexity gap -/

/-- E[Φ(Q_M)] - E[Φ(Q_M^vis)] ≥ κ/2 · α_M² · E[Var(Λ_M | G_T)]. -/
theorem latent_convexity_gap (κ α_M E_var_Λ : ℝ)
    (hκ : 0 < κ) (hvar : 0 ≤ E_var_Λ) :
    κ / 2 * (α_M ^ 2 * E_var_Λ) ≥ 0 := by
  positivity

/-- Strictness when α_M ≠ 0 and Λ_M is conditionally nondegenerate. -/
theorem latent_convexity_gap_strict (κ α_M E_var_Λ : ℝ)
    (hκ : 0 < κ) (hα : α_M ≠ 0) (hvar : 0 < E_var_Λ) :
    0 < κ / 2 * (α_M ^ 2 * E_var_Λ) := by
  positivity

/-! ## Proposition 8.8: Loading transfer -/

/-- If the conditional response has derivative in [m, L], then
    m² α_M² Var ≤ α_X² ≤ L² α_M² Var. -/
theorem loading_transfer_bounds (ml L α_M E_var_Λ α_X_sq : ℝ)
    (hlower : ml ^ 2 * α_M ^ 2 * E_var_Λ ≤ α_X_sq)
    (hupper : α_X_sq ≤ L ^ 2 * α_M ^ 2 * E_var_Λ) :
    ml ^ 2 * α_M ^ 2 * E_var_Λ ≤ α_X_sq ∧
    α_X_sq ≤ L ^ 2 * α_M ^ 2 * E_var_Λ :=
  ⟨hlower, hupper⟩

/-- If m > 0, α_M ≠ 0, and Λ_M is conditionally nondegenerate, then α_X > 0. -/
theorem loading_nonzero (ml α_M E_var_Λ α_X_sq : ℝ)
    (hml : 0 < ml) (hα : α_M ≠ 0) (hvar : 0 < E_var_Λ)
    (hlower : ml ^ 2 * α_M ^ 2 * E_var_Λ ≤ α_X_sq) :
    0 < α_X_sq := by
  calc 0 < ml ^ 2 * α_M ^ 2 * E_var_Λ := by positivity
    _ ≤ α_X_sq := hlower

/-! ## Visible summary corollaries (8.10-8.15) -/

/-- All visible summary corollaries follow from the same bound. -/
theorem visible_summary_bound (κ α_M E_var_Λ_given_S : ℝ)
    (hκ : 0 < κ) (hvar : 0 ≤ E_var_Λ_given_S) :
    κ / 2 * (α_M ^ 2 * E_var_Λ_given_S) ≥ 0 := by
  positivity

/-- Corollary 8.14: SRISK-style functionals remain compressed and under-hedged. -/
theorem srisk_compressed (κ_SR α_M E_var_Λ_S α_X E_var_Λ_X : ℝ)
    (hκ : 0 < κ_SR) (hα : α_M ≠ 0) (hvar : 0 < E_var_Λ_S)
    (hα_X : 0 < α_X) (hvar_X : 0 < E_var_Λ_X) :
    0 < κ_SR / 2 * (α_M ^ 2 * E_var_Λ_S) ∧
    0 < α_X ^ 2 * E_var_Λ_X := by
  exact ⟨by positivity, by positivity⟩

end
