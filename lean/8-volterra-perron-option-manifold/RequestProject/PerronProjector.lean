/-
  ## Perron Spectral Projector and Gauge Invariance

  Formalization of Definition 3.9 (Perron spectral projector) and
  Proposition 3.10 (Gauge invariance of the Perron projector) from

    J. Vidal Llauradó, "Volterra–Perron Pricing of the Option Manifold" (2026).

  The Perron projector Π_A := e_A ⊗ ℓ_A is the rank-one operator x ↦ e · ℓ(x).
  Proposition 3.10 states:
    (1) Π is invariant under reciprocal scaling e ↦ c·e, ℓ ↦ c⁻¹·ℓ  (c > 0).
    (2) Under conjugation A ↦ S A S⁻¹, the projector transforms as Π ↦ S Π S⁻¹.
-/

import Mathlib

open LinearMap

set_option maxHeartbeats 800000

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-! ### Rank-one projector as a bilinear construction -/

/-- The rank-one operator `x ↦ e · ℓ(x)`, modeling the Perron spectral projector `Π_A = e ⊗ ℓ`. -/
noncomputable def rankOneProj (e : V) (ell : V →ₗ[𝕜] 𝕜) : V →ₗ[𝕜] V :=
  ell.smulRight e

/-
**Proposition 3.10(1): Reciprocal-scaling invariance.**
  `rankOneProj (c • e) (c⁻¹ • ℓ) = rankOneProj e ℓ` for `c ≠ 0`.
-/
theorem rankOneProj_reciprocal_scaling
    (e : V) (ell : V →ₗ[𝕜] 𝕜) (c : 𝕜) (hc : c ≠ 0) :
    rankOneProj (c • e) (c⁻¹ • ell) = rankOneProj e ell := by
  -- By definition of rankOneProj, we have:
  unfold rankOneProj
  ext x

  -- Now let's simplify the expression (c⁻¹ • ell x) • (c • e):
  field_simp [hc]
  ring;
  simp +decide [ smul_smul, mul_comm, hc ]

/-
**Proposition 3.10(2): Conjugation covariance.**
  If `S` is an invertible linear map and `Ã = S ∘ A ∘ S⁻¹`, then
  `Π_{Ã} = S ∘ Π_A ∘ S⁻¹`.  Here we prove the rank-one projector identity:
  `rankOneProj (S e) (ℓ ∘ S⁻¹) = S ∘ (rankOneProj e ℓ) ∘ S⁻¹`.
-/
theorem rankOneProj_conjugation
    (e : V) (ell : V →ₗ[𝕜] 𝕜) (S : V ≃ₗ[𝕜] V) :
    rankOneProj (S e) (ell.comp S.symm.toLinearMap) =
      S.toLinearMap.comp ((rankOneProj e ell).comp S.symm.toLinearMap) := by
  ext xProj;
  simp +decide [ rankOneProj ]

/-
The normalization is preserved under conjugation: if `ℓ(e) = 1` and we set
  `e' = S e`, `ℓ' = ℓ ∘ S⁻¹`, then `ℓ'(e') = 1`.
-/
theorem perron_normalization_preserved
    (e : V) (ell : V →ₗ[𝕜] 𝕜) (S : V ≃ₗ[𝕜] V)
    (hnorm : ell e = 1) :
    (ell.comp S.symm.toLinearMap) (S e) = 1 := by
  aesop

/-
Idempotency of the Perron projector when `ℓ(e) = 1`.
-/
theorem rankOneProj_idempotent
    (e : V) (ell : V →ₗ[𝕜] 𝕜)
    (hnorm : ell e = 1) :
    (rankOneProj e ell).comp (rankOneProj e ell) = rankOneProj e ell := by
  -- By definition of composition of linear maps, we have
  ext x
  simp [rankOneProj, hnorm]