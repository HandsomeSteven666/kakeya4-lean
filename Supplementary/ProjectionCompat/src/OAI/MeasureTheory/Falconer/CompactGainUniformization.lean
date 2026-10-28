import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Internal compactness lemma for choosing a common cap-loss budget, gain,
and depth threshold on a closed exponent interval. It does not assert a
projection estimate: that must come from the actual one-step theorem. -/

namespace Kakeya4.Hard.MultiplicativeConvolution
open Set

theorem exists_uniform_gain_cover {a b : ℝ} (hab : a ≤ b)
    (loss gain : ℝ → ℝ) (depth : ℝ → ℕ)
    (hloss : ∀ q ∈ Icc a b, 0 < loss q)
    (hgain : ∀ q ∈ Icc a b, 0 < gain q) :
    ∃ E G : ℝ, 0 < E ∧ 0 < G ∧ ∃ N : ℕ,
      ∀ p ∈ Icc a b, ∃ q ∈ Icc a b,
        |p-q| < loss q / 4 ∧ |p-q| < gain q / 4 ∧
        E ≤ loss q / 4 ∧ G ≤ gain q / 2 ∧ depth q ≤ N := by
  classical
  let K := Icc a b
  let radius : K → ℝ := fun q => min (loss q / 4) (gain q / 4)
  have hrad (q : K) : 0 < radius q :=
    lt_min (div_pos (hloss q q.2) (by norm_num))
      (div_pos (hgain q q.2) (by norm_num))
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover
    (fun q : K => Metric.ball (q : ℝ) (radius q))
    (fun _ => Metric.isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p,hp⟩, by simpa using hrad ⟨p,hp⟩⟩)
  have hFne : F.Nonempty := by
    obtain ⟨q,hq,_⟩ := mem_iUnion₂.mp (hF (left_mem_Icc.mpr hab))
    exact ⟨q,hq⟩
  let E := F.inf' hFne (fun q => loss q / 4)
  let G := F.inf' hFne (fun q => gain q / 2)
  have hE : 0 < E := (Finset.lt_inf'_iff hFne).mpr (by
    intro q _; exact div_pos (hloss q q.2) (by norm_num))
  have hG : 0 < G := (Finset.lt_inf'_iff hFne).mpr (by
    intro q _; exact div_pos (hgain q q.2) (by norm_num))
  refine ⟨E,G,hE,hG,F.sup (fun q => depth q),?_⟩
  intro p hp
  obtain ⟨q,hq,hpq⟩ := mem_iUnion₂.mp (hF hp)
  have hdist : |p-(q:ℝ)| < radius q := by simpa [Real.dist_eq] using hpq
  refine ⟨q,q.2,hdist.trans_le (min_le_left _ _),
    hdist.trans_le (min_le_right _ _),?_,?_,?_⟩
  · exact Finset.inf'_le _ hq
  · exact Finset.inf'_le _ hq
  · exact Finset.le_sup (s := F) (f := fun q : K => depth (q : ℝ)) hq

end Kakeya4.Hard.MultiplicativeConvolution
