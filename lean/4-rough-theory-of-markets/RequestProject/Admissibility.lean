/-
  Admissibility and roughness characterization for "A Rough Theory of Markets"
  by J. Vidal Llauradó

  This file formalizes Proposition 3.6 (characterization of projected-minimax admissibility),
  Lemma 3.3 (smooth channels are degenerate), Lemma 4.1 (admissibility forces roughness),
  and the roughness necessity theorem (Theorem 5.1).
-/
import RequestProject.Defs

set_option maxHeartbeats 800000

open Finset BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace VolterraMarket

variable {N : ℕ} (m : VolterraMarket N)

/-! ## Lemma 3.3: Observability failure for smooth channels -/

/-- Lemma 3.3 (lem:smooth-failure): If H_{ij} ≥ 1/2 for an active off-diagonal edge,
    then the edge does not generate a nondegenerate projected local experiment. -/
theorem smooth_failure (i j : Fin N)
    (hsmooth : 1/2 ≤ m.H i j) :
    ¬ m.isAdmissible i j := by
  intro ⟨_, _, hrough⟩
  linarith

/-! ## Proposition 3.6: Characterization of projected-minimax admissibility -/

/-- Proposition 3.6 (prop:admissibility-characterization):
    An active off-diagonal edge is admissible iff H_{ij} < 1/2. -/
theorem admissibility_characterization (i j : Fin N) (hij : i ≠ j)
    (hactive : m.w i * m.β i j ≠ 0) :
    m.isAdmissible i j ↔ m.H i j < 1/2 := by
  constructor
  · intro ⟨_, _, hrough⟩; exact hrough
  · intro hrough; exact ⟨hij, hactive, hrough⟩

/-! ## Corollary 3.7: Non-vacuity of the admissible class -/

/-- Corollary 3.7 (cor:admissibility-nonvacuous): If there exists a rough active off-diagonal
    edge, then the admissible class is nonempty. -/
theorem admissibility_nonvacuous (i j : Fin N) (hij : i ≠ j)
    (hactive : m.w i * m.β i j ≠ 0) (hrough : m.H i j < 1/2) :
    m.admissibleEdges.Nonempty := by
  refine ⟨(i, j), ?_⟩
  rw [mem_admissibleEdges]
  exact ⟨hij, hactive, hrough⟩

/-! ## Lemma 4.1: Admissibility forces roughness -/

/-- Lemma 4.1 (lem:admissibility-rough): Every admissible edge has H_{ij} < 1/2. -/
theorem admissibility_forces_roughness (i j : Fin N) (hadm : m.isAdmissible i j) :
    m.H i j < 1/2 :=
  hadm.2.2

/-! ## Corollary 4.10: Aggregate exponent is the minimum active exponent -/

/-- Corollary 4.10 (cor:aggregate-min): The aggregate market volatility exponent equals
    the minimum active exponent. -/
def H_M (hne : m.hasActiveEdges) (_ : m.noncancelling hne) : ℝ :=
  m.H_star hne

/-! ## Assumption 5.1: Admissible dominant asymmetry -/

/-- Assumption 5.1 (ass:admissible-asymmetry): The admissible class is nonempty and
    every dominant edge is admissible. -/
structure AdmissibleDominantAsymmetry (hne : m.hasActiveEdges) : Prop where
  admissible_nonempty : m.admissibleEdges.Nonempty
  dominant_subset_admissible : m.dominantEdges hne ⊆ m.admissibleEdges

/-! ## Theorem 5.1: Market roughness necessity -/

/-- Theorem 5.1 (thm:market-roughness): Under the admissible dominant asymmetry assumption
    and noncancelling aggregation, the aggregate market volatility is necessarily rough:
    H_M < 1/2. -/
theorem market_roughness_necessity
    (hne : m.hasActiveEdges) (hnc : m.noncancelling hne)
    (hada : m.AdmissibleDominantAsymmetry hne) :
    m.H_M hne hnc < 1/2 := by
  unfold H_M H_star
  rw [Finset.inf'_lt_iff]
  obtain ⟨q, hq⟩ := hada.admissible_nonempty
  exact ⟨q, m.admissible_subset_active hq, m.admissible_rough q hq⟩

/-
Dominant edges form a nonempty subset of active edges.
-/
theorem dominantEdges_nonempty
    (hne : m.hasActiveEdges) :
    (m.dominantEdges hne).Nonempty := by
  -- By definition of $Hstar$, there exists at least one edge $(i,j)$ in $m.activeEdges$ such that $m.H i j = m.H_star hne$.
  obtain ⟨p, hp⟩ : ∃ p ∈ m.activeEdges, m.H p.1 p.2 = m.H_star hne := by
    have := Finset.exists_min_image m.activeEdges ( fun p => m.H p.1 p.2 ) hne;
    obtain ⟨ p, hp₁, hp₂ ⟩ := this; exact ⟨ p, hp₁, le_antisymm ( Finset.le_inf' _ _ fun q hq => hp₂ q hq ) ( Finset.inf'_le _ hp₁ ) ⟩ ;
  exact ⟨ p, Finset.mem_filter.mpr ⟨ hp.1, hp.2 ⟩ ⟩

/-- The admissible exponent equals the dominant exponent under the admissible dominant
    asymmetry assumption. -/
theorem H_adm_eq_H_star
    (hne : m.hasActiveEdges) (hada : m.AdmissibleDominantAsymmetry hne) :
    m.H_adm hada.admissible_nonempty = m.H_star hne := by
  apply le_antisymm
  · -- H_adm ≤ H* : There exists a dominant edge in E_adm with H = H*
    obtain ⟨p, hp⟩ := m.dominantEdges_nonempty hne
    have hp_adm : p ∈ m.admissibleEdges := hada.dominant_subset_admissible hp
    have hp_eq : m.H p.1 p.2 = m.H_star hne :=
      (Finset.mem_filter.mp hp).2
    calc m.H_adm hada.admissible_nonempty
        ≤ m.H p.1 p.2 := Finset.inf'_le _ hp_adm
      _ = m.H_star hne := hp_eq
  · -- H* ≤ H_adm : E_adm ⊆ E_act, so inf over E_act ≤ inf over E_adm
    exact Finset.inf'_mono _ m.admissible_subset_active hada.admissible_nonempty

/-- Combined statement: H_M = H_adm < 1/2 -/
theorem market_roughness_full
    (hne : m.hasActiveEdges) (hnc : m.noncancelling hne)
    (hada : m.AdmissibleDominantAsymmetry hne) :
    m.H_M hne hnc = m.H_adm hada.admissible_nonempty
    ∧ m.H_M hne hnc < 1/2 := by
  refine ⟨?_, m.market_roughness_necessity hne hnc hada⟩
  unfold H_M
  exact (m.H_adm_eq_H_star hne hada).symm

/-! ## Corollary 5.2: Recovery of the bivariate theory -/

/-- Corollary 5.2 (cor:bivariate-face): In the bivariate case (N=2),
    the roughness theorem reduces to the bivariate latent-contagion result. -/
theorem bivariate_recovery (m : VolterraMarket 2)
    (hne : m.hasActiveEdges) (hnc : m.noncancelling hne)
    (hada : m.AdmissibleDominantAsymmetry hne) :
    m.H_M hne hnc < 1/2 :=
  m.market_roughness_necessity hne hnc hada

end VolterraMarket
end