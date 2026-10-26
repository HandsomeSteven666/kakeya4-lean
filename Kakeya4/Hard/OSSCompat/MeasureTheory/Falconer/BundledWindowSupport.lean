






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.BundledAngularExtension
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! OpenAI math Apache-2.0, exact pin 1581d4cbdd69a0faf34b2089614fe2a814316a6a. See COPYING and WINDOW_PROVENANCE.json. Unchanged supporting proof bodies in independent sections. -/

section WindowSupportScope0


namespace OAI

/-! # Combining the two original orientations without normalizing pair fibers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem intersect_radial_orientations (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G H K : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hH : MeasurableSet H) (hK : MeasurableSet K)
    (hHG : H ⊆ G) (_hKG : K ⊆ Prod.swap ⁻¹' G)
    {a b C r : ℝ≥0∞} {δ : ℝ}
    (hHcost : (μ.prod ν) (G \ H) ≤ a)
    (hKcost : (ν.prod μ) ((Prod.swap ⁻¹' G) \ K) ≤ b)
    (hHcap : ∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ δ} ≤ C)
    (hKcap : ∀ z u : Space d, ν {x | (x,z) ∈ K ∧ ‖normalize (x-z)-u‖ ≤ δ} ≤ r) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ a+b ∧
      (∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ δ} ≤ C) ∧
      (∀ z u : Space d, ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ δ} ≤ r) := by
  let G' := H ∩ (Prod.swap ⁻¹' K)
  refine ⟨G',hH.inter (hK.preimage measurable_swap),fun z hz => hHG hz.1,?_,?_,?_⟩
  · have hsub : G \ G' ⊆ (G \ H) ∪ (Prod.swap ⁻¹' ((Prod.swap ⁻¹' G) \ K)) := by
      intro z hz
      by_cases hh : z ∈ H
      · right
        exact ⟨hz.1,fun hk => hz.2 ⟨hh,hk⟩⟩
      · exact Or.inl ⟨hz.1,hh⟩
    apply (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    apply add_le_add hHcost
    rw [← Measure.map_apply measurable_swap ((hG.preimage measurable_swap).diff hK),Measure.prod_swap]
    exact hKcost
  · intro x u
    apply le_trans _ (hHcap x u)
    exact measure_mono (fun _ hz => ⟨hz.1.1,hz.2⟩)
  · intro z u
    apply le_trans _ (hKcap z u)
    exact measure_mono (fun _ hz => ⟨hz.1.2,hz.2⟩)

end Falconer

end OAI

end WindowSupportScope0

section WindowSupportScope1


namespace OAI

/-! # Intersecting finitely many two-sided radial refinements -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem finite_radial_refinement (μ ν : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (I : Finset ℕ) (cost bound : ℕ → ℝ≥0∞) (radius : ℕ → ℝ)
    (hlocal : ∀ j ∈ I, ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost j ∧
      (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
      (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j)) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ ∑ j ∈ I, cost j ∧
      ∀ j ∈ I,
        (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
        (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j) := by
  classical
  have hex : ∀ j : ℕ, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (j ∈ I → H ⊆ G ∧ (μ.prod ν) (G \ H) ≤ cost j ∧
        (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
        (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j)) := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨H,hH,hsub,hd,hc⟩ := hlocal j hj
      exact ⟨H,hH,fun _ => ⟨hsub,hd,hc⟩⟩
    · exact ⟨G,hG,fun h => (hj h).elim⟩
  choose H hH hrest using hex
  let B := ⋃ j ∈ I, G \ H j
  let K := G \ B
  have hK : MeasurableSet K := hG.diff (Finset.measurableSet_biUnion I (fun j _ => hG.diff (hH j)))
  have hsub (j : ℕ) (hj : j ∈ I) : K ⊆ H j := by
    intro z hz
    by_contra hn
    exact hz.2 (mem_iUnion₂.mpr ⟨j,hj,hz.1,hn⟩)
  refine ⟨K,hK,sdiff_subset,?_,?_⟩
  · have hdiff : G \ K ⊆ B := by
      intro z hz
      by_contra hn
      exact hz.2 ⟨hz.1,hn⟩
    exact (measure_mono hdiff).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum (fun j hj => (hrest j hj).2.1)))
  · intro j hj
    refine ⟨?_,?_⟩
    · intro x u
      apply le_trans _ ((hrest j hj).2.2.1 x u)
      exact measure_mono (fun _ hz => ⟨hsub j hj hz.1,hz.2⟩)
    · intro z u
      apply le_trans _ ((hrest j hj).2.2.2 z u)
      exact measure_mono (fun _ hz => ⟨hsub j hj hz.1,hz.2⟩)

end Falconer

end OAI

end WindowSupportScope1

section WindowSupportScope2



namespace OAI

/-! # Quantitative estimates on the retained interval of dyadic scales -/

namespace Falconer
open scoped BigOperators ENNReal

lemma radial_scale_window_half {K N : ℕ} (hK : 0 < K) (hN : 2*K ≤ N) :
    N ≤ 2*K*(N/K) := by
  have hq : 2 ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by omega)
  have hr := Nat.mod_lt N hK
  have he := Nat.div_add_mod N K
  nlinarith

lemma radial_scale_window_loss {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^N)^(a/(2*(K:ℝ))) ≤ ((2:ℝ)^j)^a := by
  have he : (N:ℝ) ≤ 2*(K:ℝ)*(j:ℝ) := by
    exact_mod_cast (radial_scale_window_half hK hN).trans (Nat.mul_le_mul_left (2*K) hj)
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ) < 2*K)).mp
  have hh := mul_le_mul_of_nonneg_right he ha
  calc
    (2*K)*((N:ℝ)*(a/(2*(K:ℝ)))) = (N:ℝ)*a := by field_simp
    _ ≤ (2*(K:ℝ)*(j:ℝ))*a := hh
    _ = (2*K)*((j:ℝ)*a) := by ring

lemma radial_scale_window_decay {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^j)^(-a) ≤ ((2:ℝ)^N)^(-(a/(2*(K:ℝ)))) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact inv_anti₀ (by positivity) (radial_scale_window_loss hK hN hj ha)

theorem radial_scale_window_cost (K : ℕ) (hK : 0 < K) {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∑ j ∈ Finset.Icc (N/K) N, ENNReal.ofReal (((2:ℝ)^j)^(-a))) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  let c : ℝ := a/(4*(K:ℝ))
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Np,hp⟩ := PlanarFalconer.fixed_polynomial_subpower 1 hc
  refine ⟨c,hc,2*K+Np,?_⟩
  intro N hN
  have hhalf : 2*K ≤ N := by omega
  have hpoly : (N:ℝ)+1 ≤ ((2:ℝ)^N)^c := by
    apply le_trans _ (hp N (by omega))
    simp only [pow_one]
    linarith [show (0:ℝ) ≤ N by positivity]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (N/K) N,
        ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ENNReal.ofReal_le_ofReal (radial_scale_window_decay hK hhalf
        (Finset.mem_Icc.mp hj).1 ha.le)
    _ = ((Finset.Icc (N/K) N).card:ℝ≥0∞)*
        ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by simp
    _ ≤ ((N:ℝ≥0∞)+1)*ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      gcongr
      exact_mod_cast (show (Finset.Icc (N/K) N).card ≤ N+1 by simp)
    _ = ENNReal.ofReal (((N:ℝ)+1)*((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (by positivity) (by norm_num)]
      simp
    _ ≤ ENNReal.ofReal (((2:ℝ)^N)^c*((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpoly (by positivity))
    _ = _ := by
      rw [← Real.rpow_add (by positivity)]
      congr 2
      dsimp [c]
      ring

end Falconer

end OAI

end WindowSupportScope2

section WindowSupportScope3


namespace OAI

/-! # Intersecting the actual pair sets at finitely many radial scales -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem finite_radial_scale_intersection (μ ν : Measure (Space d))
    (I : Finset ℕ) (G : ℕ → Set (Space d × Space d))
    (t C : ℕ → ℝ≥0∞) (r : ℕ → ℝ)
    (hG : ∀ j ∈ I, MeasurableSet (G j))
    (hcost : ∀ j ∈ I, (ν.prod μ) (G j)ᶜ ≤ t j)
    (hcap : ∀ j ∈ I, ∀ x u : Space d,
      μ {z | (x,z) ∈ G j ∧ ‖normalize (z-x)-u‖ ≤ r j} ≤ C j) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (ν.prod μ) Hᶜ ≤ ∑ j ∈ I, t j ∧
      ∀ j ∈ I, ∀ s : ℝ, s ≤ r j → ∀ x u : Space d,
        μ {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ s} ≤ C j := by
  classical
  let H := ⋂ j ∈ I, G j
  have hm : MeasurableSet H := Finset.measurableSet_biInter I hG
  refine ⟨H,hm,?_,?_⟩
  · have he : Hᶜ = ⋃ j ∈ I, (G j)ᶜ := by
      ext p
      simp only [H,mem_compl_iff,mem_iInter,mem_iUnion]
      push Not
      constructor <;> rintro ⟨j,hj,hp⟩ <;> exact ⟨j,hj,hp⟩
    rw [he]
    exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hcost)
  · intro j hj s hs x u
    apply (measure_mono ?_).trans (hcap j hj x u)
    intro z hz
    exact ⟨mem_iInter₂.mp hz.1 j hj,hz.2.trans hs⟩

end Falconer

end OAI

end WindowSupportScope3

section WindowSupportScope4



namespace OAI

/-! # Selecting a retained dyadic scale for an arbitrary cap radius -/

namespace Falconer

theorem radial_dyadic_bracket (N : ℕ) {r : ℝ}
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hr1 : r ≤ 1) :
    ∃ j ≤ N, r ≤ ((2:ℝ)^j)⁻¹ ∧ ((2:ℝ)^j)⁻¹ < 2*r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hr0 hr1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have he : (1/2:ℝ)^j = ((2:ℝ)^j)⁻¹ := by rw [one_div,inv_pow]
  rw [he] at hhi
  have hj : j ≤ N := by
    by_contra h
    have hp : (2:ℝ)^N < (2:ℝ)^j := pow_lt_pow_right₀ (by norm_num) (by omega)
    have hi : ((2:ℝ)^j)⁻¹ < ((2:ℝ)^N)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by positivity)).mpr hp
    exact (not_lt_of_ge hr) (hhi.trans_lt hi)
  refine ⟨j,hj,hhi,?_⟩
  rw [pow_succ,he] at hlo
  linarith

theorem radial_dyadic_bracket_above (N B : ℕ) {r : ℝ}
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hrB : r ≤ ((2:ℝ)^B)⁻¹) :
    ∃ j, B ≤ j ∧ j ≤ N ∧ r ≤ ((2:ℝ)^j)⁻¹ ∧ ((2:ℝ)^j)⁻¹ < 2*r := by
  have hr1 : r ≤ 1 := hrB.trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  obtain ⟨j,hj,hhi,hlo⟩ := radial_dyadic_bracket N hr hr1
  have hBj : B ≤ j := by
    by_contra h
    have hp : (2:ℝ)^(j+1) ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) (by omega)
    have hinv : ((2:ℝ)^B)⁻¹ ≤ ((2:ℝ)^(j+1))⁻¹ := inv_anti₀ (by positivity) hp
    have he : ((2:ℝ)^(j+1))⁻¹ = ((2:ℝ)^j)⁻¹/2 := by rw [pow_succ,mul_inv_rev]; ring
    rw [he] at hinv
    linarith
  exact ⟨j,hBj,hj,hhi,hlo⟩

end Falconer

end OAI

end WindowSupportScope4

section WindowSupportScope5




namespace OAI

/-! # From a window of improved dyadic caps to every radius -/

namespace Falconer
open scoped ENNReal

theorem dyadic_window_interpolation (f : ℝ → ℝ≥0∞) (hf : Monotone f)
    (hmass : ∀ r : ℝ, f r ≤ 1) {N m : ℕ} (_hmN : m ≤ N)
    {e q v : ℝ} (hq : 0 ≤ q) (hqv : q ≤ v)
    (hcoarse : (m:ℝ)*q ≤ (N:ℝ)*e)
    (hconstant : (2:ℝ)^v ≤ ((2:ℝ)^N)^e)
    (hdyadic : ∀ j : ℕ, m ≤ j → j ≤ N → f (1/(2:ℝ)^j) ≤
      ENNReal.ofReal ((1/(2:ℝ)^j)^v))
    {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
    f r ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hc : 1/(2:ℝ)^m ≤ r
  · apply (hmass r).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hp := dyadic_relative_scale_bound m N hcoarse
    have hi : ((2:ℝ)^m)^q*(1/(2:ℝ)^m)^q = 1 := by
      rw [one_div,Real.inv_rpow (by positivity)]
      exact mul_inv_cancel₀ (by positivity)
    calc
      1 = ((2:ℝ)^m)^q*(1/(2:ℝ)^m)^q := hi.symm
      _ ≤ ((2:ℝ)^N)^e*r^q := mul_le_mul hp
        (Real.rpow_le_rpow (by positivity) hc hq) (by positivity) (by positivity)
  · obtain ⟨j,hj,hrj,hjr⟩ := Regularization.dyadic_radius_bracket hr hr1
    have hmj : m ≤ j := by
      by_contra hn
      have hjm : j+1 ≤ m := by omega
      have hd : 1/(2:ℝ)^m ≤ 1/(2:ℝ)^(j+1) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hjm)
      have he : 1/(2:ℝ)^j = 2*(1/(2:ℝ)^(j+1)) := by rw [pow_succ]; field_simp
      have hh : 1/(2:ℝ)^(j+1) ≤ r := by rw [he] at hjr; linarith only [hjr]
      exact hc (hd.trans hh)
    apply ((hf hrj).trans (hdyadic j hmj hj)).trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ (2*r)^v := Real.rpow_le_rpow (by positivity) hjr (hq.trans hqv)
      _ = (2:ℝ)^v*r^v := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ ((2:ℝ)^N)^e*r^q := mul_le_mul hconstant
        (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hqv) (by positivity) (by positivity)

end Falconer

end OAI

end WindowSupportScope5

section WindowSupportScope6



namespace OAI

/-! # Turning the improved scale window into the manuscript's radial cap bound -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem exists_radial_window_denominator {e q : ℝ} (he : 0 < e) (hq : 0 ≤ q) :
    ∃ K : ℕ, 0 < K ∧ ∀ N : ℕ, ((N/K:ℕ):ℝ)*q ≤ (N:ℝ)*e := by
  obtain ⟨K,hK⟩ := exists_nat_gt (q/e)
  have hKe : q < (K:ℝ)*e := (div_lt_iff₀ he).mp hK
  have hKpos : 0 < K := by
    have hh : (0:ℝ) < K := lt_of_le_of_lt (div_nonneg hq he.le) hK
    exact_mod_cast hh
  refine ⟨K,hKpos,fun N => ?_⟩
  have hKr : (0:ℝ) < K := by exact_mod_cast hKpos
  calc
    _ ≤ ((N:ℝ)/(K:ℝ))*q := mul_le_mul_of_nonneg_right Nat.cast_div_le hq
    _ ≤ ((N:ℝ)/(K:ℝ))*((K:ℝ)*e) := mul_le_mul_of_nonneg_left hKe.le (by positivity)
    _ = _ := by field_simp

theorem radialCapBound_of_window {d N m : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (G : Set (Space d × Space d))
    (hmN : m ≤ N) {e q v : ℝ} (hq : 0 ≤ q) (hqv : q ≤ v)
    (hcoarse : (m:ℝ)*q ≤ (N:ℝ)*e)
    (hconstant : (2:ℝ)^v ≤ ((2:ℝ)^N)^e)
    (hdyadic : ∀ j : ℕ, m ≤ j → j ≤ N →
      (∀ x u : Space d, (μ : Measure (Space d))
        {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^j)^v)) ∧
      (∀ z u : Space d, (ν : Measure (Space d))
        {x | (z,x) ∈ G ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^j)^v))) : RadialCapBound μ ν G N e q := by
  have hμ (x w : Space d) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      (μ : Measure (Space d)) {z | (z,x) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤
        ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
    apply dyadic_window_interpolation
      (fun r => (μ : Measure (Space d)) {z | (z,x) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r})
      (fun _ _ hrs => measure_mono (fun _ hz => ⟨hz.1,hz.2.trans hrs⟩))
      (fun r => (measure_mono (subset_univ _)).trans_eq (measure_univ)) hmN hq hqv hcoarse hconstant
      (fun j hj hjN => (hdyadic j hj hjN).1 x w) hr hr1
  have hν (z w : Space d) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      (ν : Measure (Space d)) {x | (z,x) ∈ G ∧ ‖normalize (x-z)-w‖ ≤ r} ≤
        ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
    apply dyadic_window_interpolation
      (fun r => (ν : Measure (Space d)) {x | (z,x) ∈ G ∧ ‖normalize (x-z)-w‖ ≤ r})
      (fun _ _ hrs => measure_mono (fun _ hz => ⟨hz.1,hz.2.trans hrs⟩))
      (fun r => (measure_mono (subset_univ _)).trans_eq (measure_univ)) hmN hq hqv hcoarse hconstant
      (fun j hj hjN => (hdyadic j hj hjN).2 z w) hr hr1
  constructor
  · intro x _ w _ r hr hr1
    change (ν : Measure (Space d)) {y | (x,y) ∈ G ∧ ‖normalize (y-x)-w‖ < r} ≤ _
    apply le_trans _ (hν x w (by simpa only [one_div] using hr) hr1)
    exact measure_mono (fun _ hz => ⟨hz.1,hz.2.le⟩)
  · intro y _ w _ r hr hr1
    change (μ : Measure (Space d)) {x | (x,y) ∈ G ∧ ‖normalize (x-y)-w‖ < r} ≤ _
    apply le_trans _ (hμ y w (by simpa only [one_div] using hr) hr1)
    exact measure_mono (fun _ hz => ⟨hz.1,hz.2.le⟩)

end Falconer

end OAI

end WindowSupportScope6
