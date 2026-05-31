/-
# Synchronized Stress Relative Value — Core Definitions

Formalization of definitions and basic structures from:
"Synchronized Stress Relative Value: Public-Neutral Option Books under Latent Stress Compression"
by J. Vidal Llauradó (2026).
-/
import Mathlib

open scoped BigOperators

noncomputable section

/-! ## Definition 3.1: Public-neutral listed-option book -/

/-- A listed-option book `x` is `ε`-public-neutral w.r.t. the public risk map `A`
    if `|A x| ≤ ε` coordinatewise. (Definition 3.1) -/
def IsPublicNeutral {n q : ℕ} (A : Matrix (Fin q) (Fin n) ℝ) (epsilon : Fin q → ℝ)
    (x : Fin n → ℝ) : Prop :=
  ∀ j : Fin q, |∑ i, A j i * x i| ≤ epsilon j

/-- A listed-option book is exactly public-neutral if `ε = 0`. (Definition 3.1) -/
def IsExactlyPublicNeutral {n q : ℕ} (A : Matrix (Fin q) (Fin n) ℝ)
    (x : Fin n → ℝ) : Prop :=
  IsPublicNeutral A 0 x

/-! ## Definition 4.2: Variance-dollar synchronization edge -/

/-- The variance-dollar synchronization edge. (Definition 4.2)
    `ΔV_sync = π_sync * D_imp` where `π_sync = ρ_imp - ρ̂_real`. -/
def varianceDollarSyncEdge (rho_imp rho_real D_imp : ℝ) : ℝ :=
  (rho_imp - rho_real) * D_imp

/-- The cost-adjusted book edge. (Definition 4.2)
    `μ̂_book = N_sync * ΔV_sync - TC - Carry - HE - Tail` -/
def costAdjustedBookEdge (N_sync ΔV_sync TC Carry HE Tail : ℝ) : ℝ :=
  N_sync * ΔV_sync - TC - Carry - HE - Tail

/-! ## Definition 6.1: Sellability lower bound -/

/-- The sellability lower bound for a cell. (Definition 6.1)
    `LB = μ̂_book - z_α * σ̂_model - TC_round - Tail_reserve` -/
def sellabilityLB (mu_book z_alpha sigma_model TC_round Tail_reserve : ℝ) : ℝ :=
  mu_book - z_alpha * sigma_model - TC_round - Tail_reserve

/-! ## Definition 6.3: Book-risk denominator -/

/-- The book-risk denominator. (Definition 6.3)
    `R = max{σ̂_hist, ES_hist, TC_entry, 1, Margin_proxy}` -/
def bookRiskDenom (sigma_hist ES_hist TC_entry Margin_proxy : ℝ) : ℝ :=
  max (max (max (max sigma_hist ES_hist) TC_entry) 1) Margin_proxy

/-! ## Definition 6.4: Lower-bound size -/

/-- The unconstrained lower-bound size. (Definition 6.4)
    `x⁺ = (LB)₊ / (λ * R)` -/
def unconstrainedLBSize (LB lam R : ℝ) : ℝ :=
  max LB 0 / (lam * R)

/-- The executable (capped) lower-bound size. (Definition 6.4)
    `x_exe = min{x⁺, x̄_margin, x̄_tail, x̄_cost}` -/
def executableSize (LB lam R x_margin x_tail x_cost : ℝ) : ℝ :=
  if LB ≤ 0 then 0
  else min (min (unconstrainedLBSize LB lam R) x_margin) (min x_tail x_cost)

/-! ## Carrier basket (Definition 5.3) -/

/-- The unconstrained carrier weight for name `i`. (Definition 5.3) -/
def unconstrainedCarrierWeight {n : ℕ} (s_tilde : Fin n → ℝ) (cost : Fin n → ℝ)
    (eps : ℝ) (p q : ℝ) (i : Fin n) : ℝ :=
  let num := (max (s_tilde i) 0) ^ p / (cost i + eps) ^ q
  let denom := ∑ j, (max (s_tilde j) 0) ^ p / (cost j + eps) ^ q
  num / denom

end
