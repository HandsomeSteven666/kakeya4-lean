import Kakeya4.Hard.MultilinearKakeya.Basic

/-! The one-dimensional variation bound from finite critical-point partitioning.
Polynomial arctangent derivatives have total variation at most pi times degree,
including the integral on the entire real line. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

theorem continuous_sign_on_interval {g : ℝ → ℝ} {a b : ℝ} (hg : Continuous g)
    (hzero : ∀ x ∈ Ioo a b, g x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 ≤ g x) ∨ (∀ x ∈ Ioo a b, g x ≤ 0) := by
  by_cases hpos : ∃ x ∈ Ioo a b, 0 < g x
  · left
    obtain ⟨x, hx, hxp⟩ := hpos
    intro y hy
    by_contra! hyn
    obtain ⟨z, hz, hzg⟩ := isPreconnected_Ioo.intermediate_value hy hx hg.continuousOn
      (show (0 : ℝ) ∈ Icc (g y) (g x) from ⟨hyn.le, hxp.le⟩)
    exact hzero z hz hzg
  · right
    push Not at hpos
    exact hpos

theorem integral_norm_derivative_le_of_no_critical {f g : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b) (hderiv : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (hzero : ∀ x ∈ Ioo a b, g x ≠ 0) (hosc : ∀ x y, f x - f y ≤ B) :
    ∫ x in a..b, ‖g x‖ ≤ B := by
  have hFTC : ∫ x in a..b, g x = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hg.intervalIntegrable a b)
  rcases continuous_sign_on_interval hg hzero with hpos | hneg
  · calc
      _ = ∫ x in a..b, g x := intervalIntegral.integral_congr_Ioo_of_le hab
        (fun x hx => Real.norm_of_nonneg (hpos x hx))
      _ = f b - f a := hFTC
      _ ≤ B := hosc b a
  · calc
      _ = ∫ x in a..b, -g x := intervalIntegral.integral_congr_Ioo_of_le hab
        (fun x hx => Real.norm_of_nonpos (hneg x hx))
      _ = -(∫ x in a..b, g x) := intervalIntegral.integral_neg
      _ = f a - f b := by rw [hFTC]; ring
      _ ≤ B := hosc a b

theorem integral_norm_derivative_le_of_finite_critical {f g : ℝ → ℝ} {a b B : ℝ}
    (hderiv : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (hosc : ∀ x y, f x - f y ≤ B) (hB : 0 ≤ B)
    (S : Finset ℝ) (hab : a ≤ b)
    (hcrit : ∀ x ∈ Ioo a b, g x = 0 → x ∈ S) :
    ∫ x in a..b, ‖g x‖ ≤ (S.card + 1 : ℝ) * B := by
  classical
  induction S using Finset.strongInductionOn generalizing a b with
  | _ S ih =>
    by_cases hex : ∃ c ∈ Ioo a b, g c = 0
    · obtain ⟨c, hc, hgc⟩ := hex
      have hcS := hcrit c hc hgc
      let L := S.filter (fun x => x < c)
      let R := S.filter (fun x => c < x)
      have hL : L ⊂ S := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro heq
        have : c ∈ L := heq.symm ▸ hcS
        simp [L] at this
      have hR : R ⊂ S := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro heq
        have : c ∈ R := heq.symm ▸ hcS
        simp [R] at this
      have hl := ih L hL hc.1.le (fun x hx hzero =>
        Finset.mem_filter.mpr ⟨hcrit x ⟨hx.1, hx.2.trans hc.2⟩ hzero, hx.2⟩)
      have hr := ih R hR hc.2.le (fun x hx hzero =>
        Finset.mem_filter.mpr ⟨hcrit x ⟨hc.1.trans hx.1, hx.2⟩ hzero, hx.1⟩)
      have hdis : Disjoint L R := by
        apply Finset.disjoint_left.mpr
        intro x hl hr
        exact (lt_asymm (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hr).2)
      have hunion : L ∪ R = S.erase c := by
        ext x
        simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro (⟨hx, hlt⟩ | ⟨hx, hgt⟩)
          · exact ⟨hlt.ne, hx⟩
          · exact ⟨hgt.ne', hx⟩
        · rintro ⟨hne, hx⟩
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inl ⟨hx, hlt⟩
          · exact Or.inr ⟨hx, hgt⟩
      have hcard : L.card + R.card + 1 = S.card := by
        rw [← Finset.card_union_of_disjoint hdis, hunion]
        exact Finset.card_erase_add_one hcS
      have hcardR : (L.card : ℝ) + R.card + 1 = S.card := by exact_mod_cast hcard
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hg.norm.intervalIntegrable a c) (hg.norm.intervalIntegrable c b)]
      nlinarith
    · have hz (x : ℝ) (hx : x ∈ Ioo a b) : g x ≠ 0 := fun h => hex ⟨x, hx, h⟩
      have hbase := integral_norm_derivative_le_of_no_critical hab hderiv hg hz hosc
      nlinarith [Nat.cast_nonneg (α := ℝ) S.card]

def arctanPolynomialDerivative (q : Polynomial ℝ) (ε x : ℝ) : ℝ :=
  (1 / (1 + (q.eval x / ε)^2)) * (q.derivative.eval x / ε)

theorem hasDerivAt_arctanPolynomial (q : Polynomial ℝ) (ε x : ℝ) :
    HasDerivAt (fun t => Real.arctan (q.eval t / ε))
      (arctanPolynomialDerivative q ε x) x :=
  ((q.hasDerivAt x).div_const ε).arctan

theorem continuous_arctanPolynomialDerivative (q : Polynomial ℝ) (ε : ℝ) :
    Continuous (arctanPolynomialDerivative q ε) := by
  unfold arctanPolynomialDerivative
  apply Continuous.mul
  · exact continuous_const.div (continuous_const.add ((q.continuous.div_const ε).pow 2))
      (fun x => by positivity)
  · exact q.derivative.continuous.div_const ε

theorem arctanPolynomialDerivative_ne_zero {q : Polynomial ℝ} {ε x : ℝ}
    (hε : ε ≠ 0) (hx : q.derivative.eval x ≠ 0) :
    arctanPolynomialDerivative q ε x ≠ 0 := by
  unfold arctanPolynomialDerivative
  exact mul_ne_zero (one_div_ne_zero (by positivity)) (div_ne_zero hx hε)

theorem integral_arctanPolynomialDerivative_le_pi_of_no_critical (q : Polynomial ℝ)
    {ε a b : ℝ} (hε : ε ≠ 0) (hab : a ≤ b)
    (hcrit : ∀ x ∈ Ioo a b, q.derivative.eval x ≠ 0) :
    ∫ x in a..b, ‖arctanPolynomialDerivative q ε x‖ ≤ Real.pi := by
  apply integral_norm_derivative_le_of_no_critical hab (hasDerivAt_arctanPolynomial q ε)
    (continuous_arctanPolynomialDerivative q ε)
    (fun x hx => arctanPolynomialDerivative_ne_zero hε (hcrit x hx))
  intro x y
  linarith [Real.arctan_lt_pi_div_two (q.eval x / ε),
    Real.neg_pi_div_two_lt_arctan (q.eval y / ε)]

theorem intervalIntegral_arctanPolynomialDerivative_le_degree (q : Polynomial ℝ)
    {ε a b : ℝ} (hε : ε ≠ 0) (hab : a ≤ b) :
    ∫ x in a..b, ‖arctanPolynomialDerivative q ε x‖ ≤ q.natDegree * Real.pi := by
  classical
  by_cases hq : q.derivative = 0
  · simp only [arctanPolynomialDerivative, hq, Polynomial.eval_zero, zero_div,
      mul_zero, norm_zero, intervalIntegral.integral_zero]
    positivity
  · let S := q.derivative.roots.toFinset
    have hcrit (x : ℝ) (_hx : x ∈ Ioo a b)
        (hz : arctanPolynomialDerivative q ε x = 0) : x ∈ S := by
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hq).mpr
      by_contra hn
      exact arctanPolynomialDerivative_ne_zero hε hn hz
    have hosc (x y : ℝ) :
        Real.arctan (q.eval x / ε) - Real.arctan (q.eval y / ε) ≤ Real.pi := by
      linarith [Real.arctan_lt_pi_div_two (q.eval x / ε),
        Real.neg_pi_div_two_lt_arctan (q.eval y / ε)]
    have h := integral_norm_derivative_le_of_finite_critical
      (hasDerivAt_arctanPolynomial q ε) (continuous_arctanPolynomialDerivative q ε)
      hosc Real.pi_pos.le S hab hcrit
    have hcard : S.card + 1 ≤ q.natDegree := by
      have hc : S.card ≤ q.derivative.natDegree :=
        (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
      have hd := Polynomial.natDegree_derivative_lt (Polynomial.derivative_ne_zero.mp hq)
      omega
    have hcR : (S.card : ℝ) + 1 ≤ q.natDegree := by exact_mod_cast hcard
    exact h.trans (mul_le_mul_of_nonneg_right hcR Real.pi_pos.le)

theorem integrable_arctanPolynomialDerivative (q : Polynomial ℝ)
    {ε : ℝ} (hε : ε ≠ 0) : Integrable (arctanPolynomialDerivative q ε) := by
  apply integrable_of_intervalIntegral_norm_bounded (q.natDegree * Real.pi)
    (l := (atTop : Filter ℕ))
    (a := fun i : ℕ => -(i : ℝ)) (b := fun i : ℕ => (i : ℝ))
  · intro i
    exact ((continuous_arctanPolynomialDerivative q ε).intervalIntegrable _ _).1
  · exact tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  · exact tendsto_natCast_atTop_atTop
  · exact Eventually.of_forall (fun i => intervalIntegral_arctanPolynomialDerivative_le_degree
      q hε (by have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith))

theorem integral_arctanPolynomialDerivative_le_degree (q : Polynomial ℝ)
    {ε : ℝ} (hε : ε ≠ 0) :
    ∫ x : ℝ, ‖arctanPolynomialDerivative q ε x‖ ≤ q.natDegree * Real.pi := by
  have ha : Tendsto (fun i : ℕ => -(i : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun i : ℕ => (i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  apply le_of_tendsto (intervalIntegral_tendsto_integral
    (integrable_arctanPolynomialDerivative q hε).norm ha hb)
  exact Eventually.of_forall (fun i => intervalIntegral_arctanPolynomialDerivative_le_degree
    q hε (by have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith))

end Kakeya4.Hard.MultilinearKakeya
