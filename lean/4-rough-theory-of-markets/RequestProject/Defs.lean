/-
  Definitions for "A Rough Theory of Markets"
  by J. Vidal Llauradó

  This file formalizes the core definitions of the N-asset directed Volterra market model.
-/
import Mathlib

set_option maxHeartbeats 800000

open Finset BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Basic market structure -/

/-- An N-asset directed Volterra market with exponents H_{ij} ∈ (0,1),
    amplitudes β_{ij}, and deterministic weights w_i > 0. -/
structure VolterraMarket (N : ℕ) where
  /-- Hurst exponents H_{ij} ∈ (0,1) -/
  H : Fin N → Fin N → ℝ
  /-- Amplitudes β_{ij} -/
  β : Fin N → Fin N → ℝ
  /-- Deterministic positive weights w_i > 0 -/
  w : Fin N → ℝ
  /-- Continuity amplitudes a_{ij}(t,t) > 0 when β_{ij} ≠ 0 -/
  a_diag : Fin N → Fin N → ℝ
  /-- Exponents are in (0,1) -/
  hH_pos : ∀ i j, 0 < H i j
  hH_lt_one : ∀ i j, H i j < 1
  /-- Weights are positive -/
  hw_pos : ∀ i, 0 < w i
  /-- a_{ij}(t,t) > 0 when β_{ij} ≠ 0 -/
  ha_pos : ∀ i j, β i j ≠ 0 → 0 < a_diag i j

variable {N : ℕ}

namespace VolterraMarket

/-- The active edge set: E_act = {(i,j) : w_i * β_{ij} ≠ 0}.
    Since w_i > 0, this is equivalent to β_{ij} ≠ 0. -/
def activeEdges (m : VolterraMarket N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => m.w p.1 * m.β p.1 p.2 ≠ 0

/-- Active edge set is nonempty predicate -/
def hasActiveEdges (m : VolterraMarket N) : Prop :=
  m.activeEdges.Nonempty

/-- Off-diagonal active edges -/
def activeOffDiagEdges (m : VolterraMarket N) : Finset (Fin N × Fin N) :=
  m.activeEdges.filter fun p => p.1 ≠ p.2

/-- The dominant exponent H* = min over active edges -/
def H_star (m : VolterraMarket N) (hne : m.hasActiveEdges) : ℝ :=
  m.activeEdges.inf' hne (fun p => m.H p.1 p.2)

/-- The dominant edge set E* = {(i,j) ∈ E_act : H_{ij} = H*} -/
def dominantEdges (m : VolterraMarket N) (hne : m.hasActiveEdges) : Finset (Fin N × Fin N) :=
  m.activeEdges.filter fun p => m.H p.1 p.2 = m.H_star hne

/-- An edge (i,j) is projected-minimax admissible if:
    (i) it is an active off-diagonal edge
    (ii) H_{ij} < 1/2 (roughness condition) -/
def isAdmissible (m : VolterraMarket N) (i j : Fin N) : Prop :=
  i ≠ j ∧ m.w i * m.β i j ≠ 0 ∧ m.H i j < 1/2

/-- The admissible edge set -/
def admissibleEdges (m : VolterraMarket N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => m.isAdmissible p.1 p.2

/-- The admissible exponent H_adm = min over admissible edges -/
def H_adm (m : VolterraMarket N) (hne : m.admissibleEdges.Nonempty) : ℝ :=
  m.admissibleEdges.inf' hne (fun p => m.H p.1 p.2)

/-- w_i > 0 implies w_i * β_{ij} ≠ 0 ↔ β_{ij} ≠ 0 -/
theorem active_iff_beta_ne_zero (m : VolterraMarket N) (i j : Fin N) :
    m.w i * m.β i j ≠ 0 ↔ m.β i j ≠ 0 := by
  constructor
  · intro h hβ; exact h (by rw [hβ, mul_zero])
  · intro h; exact mul_ne_zero (ne_of_gt (m.hw_pos i)) h

/-- Membership in admissibleEdges -/
theorem mem_admissibleEdges (m : VolterraMarket N) (p : Fin N × Fin N) :
    p ∈ m.admissibleEdges ↔ m.isAdmissible p.1 p.2 := by
  simp [admissibleEdges]

/-- Admissible edges are active -/
theorem admissible_subset_active (m : VolterraMarket N) :
    m.admissibleEdges ⊆ m.activeEdges := by
  intro p hp
  rw [mem_admissibleEdges] at hp
  simp only [activeEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hp.2.1

/-- Admissible edges are off-diagonal -/
theorem admissible_off_diag (m : VolterraMarket N) (p : Fin N × Fin N)
    (hp : p ∈ m.admissibleEdges) : p.1 ≠ p.2 := by
  rw [mem_admissibleEdges] at hp
  exact hp.1

/-- Admissible edges have H < 1/2 -/
theorem admissible_rough (m : VolterraMarket N) (p : Fin N × Fin N)
    (hp : p ∈ m.admissibleEdges) : m.H p.1 p.2 < 1/2 := by
  rw [mem_admissibleEdges] at hp
  exact hp.2.2

/-! ## Noncancelling aggregation (Assumption 3.4) -/

/-- Noncancelling aggregation: the dominant short-scale contributions do not cancel. -/
def noncancelling (m : VolterraMarket N) (hne : m.hasActiveEdges) : Prop :=
  ∃ j : Fin N, (∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ m.dominantEdges hne),
    m.w i * m.β i j * m.a_diag i j) ≠ 0

/-! ## Contagion phases (Definition 7.8) -/

/-- Market contagion phase classification -/
inductive ContagionPhase where
  | smoothDegenerate    -- all active off-diag edges have H ≥ 1/2
  | roughObservable     -- admissible dominant edges, spectral radius ≤ 1
  | roughSynchronized   -- admissible dominant edges, spectral radius > 1
  | activatedSynchronized -- rough-synchronized + threshold activation
  deriving DecidableEq

end VolterraMarket
end
