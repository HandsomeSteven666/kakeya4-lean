import Kakeya4.Hard.MultilinearKakeya.Basic

/-! A dimension-explicit determinant/volume comparison for centrally symmetric
convex sets, supplying the convex-geometric part of the CV visibility bound. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem smul_mem_of_convex_symmetric {V : Type*} [AddCommGroup V] [Module ℝ V]
    {K : Set V} (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    {v : V} (hv : v ∈ K) {t : ℝ} (ht : |t| ≤ 1) : t • v ∈ K := by
  have hl := (abs_le.mp ht).1
  have hu := (abs_le.mp ht).2
  have h := hK hv (hsymm v hv) (a := (1+t)/2) (b := (1-t)/2)
    (by linarith) (by linarith) (by ring)
  have heq : ((1+t)/2) • v + ((1-t)/2) • (-v) = t • v := by module
  rwa [heq] at h

theorem matrix_box_image_subset_convex_symmetric {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) {K : Set (Fin n → ℝ)}
    (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hcol : ∀ i, (fun j => A j i) ∈ K) :
    (Matrix.toLin' A) '' Icc (fun _ => -(n : ℝ)⁻¹) (fun _ => (n : ℝ)⁻¹) ⊆ K := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rintro y ⟨x,hx,rfl⟩
  have hmem (i : Fin n) : ((n : ℝ)*x i) • (fun j => A j i) ∈ K := by
    apply smul_mem_of_convex_symmetric hK hsymm (hcol i)
    rw [abs_le]
    constructor
    · have hi := mul_le_mul_of_nonneg_left (hx.1 i) hnR.le
      nlinarith [mul_inv_cancel₀ hnR.ne']
    · have hi := mul_le_mul_of_nonneg_left (hx.2 i) hnR.le
      nlinarith [mul_inv_cancel₀ hnR.ne']
  have h := hK.sum_mem (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.mpr hnR.le) (by simp [hnR.ne']) (fun i _ => hmem i)
  have heq : (∑ i : Fin n, (n : ℝ)⁻¹ • (((n : ℝ)*x i) • (fun j => A j i))) =
      Matrix.toLin' A x := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hnR.ne']
  rwa [heq] at h

theorem determinant_volume_le_of_convex_symmetric {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) {K : Set (Fin n → ℝ)}
    (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hcol : ∀ i, (fun j => A j i) ∈ K) :
    ENNReal.ofReal (((2 : ℝ)/(n : ℝ))^n * |A.det|) ≤ volume K := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let B : Set (Fin n → ℝ) := Icc (fun _ => -(n : ℝ)⁻¹) (fun _ => (n : ℝ)⁻¹)
  have hvol : volume B = ENNReal.ofReal (((2 : ℝ)/(n : ℝ))^n) := by
    rw [Real.volume_Icc_pi]
    have heq : (n : ℝ)⁻¹ - -(n : ℝ)⁻¹ = 2/(n : ℝ) := by ring
    simp only [heq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) n).symm
  calc
    _ = ENNReal.ofReal |A.det| * volume B := by
      rw [hvol, ← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      ring
    _ = volume ((Matrix.toLin' A) '' B) := by
      rw [volume.addHaar_image_linearMap, LinearMap.det_toLin']
    _ ≤ volume K := measure_mono (matrix_box_image_subset_convex_symmetric hn A hK hsymm hcol)

/-- Scaled-vector form of the convex determinant comparison. In applications
s_i is a directional surface budget and K is the visibility unit body. -/
theorem determinant_volume_le_of_scaled_vectors {n : ℕ} (hn : 0 < n)
    (v : Fin n → Fin n → ℝ) (s : Fin n → ℝ) (hs : ∀ i, 0 < s i)
    {K : Set (Fin n → ℝ)} (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hv : ∀ i, (s i)⁻¹ • v i ∈ K) :
    ENNReal.ofReal (((2 : ℝ)/(n : ℝ))^n * |Matrix.det (fun i j => v j i)|) ≤
      volume K * ENNReal.ofReal (∏ i, s i) := by
  let V : Matrix (Fin n) (Fin n) ℝ := fun i j => v j i
  let A := V * Matrix.diagonal (fun i => (s i)⁻¹)
  have hcol (j : Fin n) : (fun i => A i j) ∈ K := by
    have heq : (fun i => A i j) = (s j)⁻¹ • v j := by
      funext i
      change (V * Matrix.diagonal (fun k => (s k)⁻¹)) i j = (s j)⁻¹ * v j i
      rw [Matrix.mul_diagonal]
      exact mul_comm _ _
    rw [heq]
    exact hv j
  have h := determinant_volume_le_of_convex_symmetric hn A hK hsymm hcol
  have hprod : 0 < ∏ i, s i := Finset.prod_pos (fun i _ => hs i)
  have hdet : |A.det| = |V.det| * (∏ i, s i)⁻¹ := by
    simp [A,Matrix.det_mul,Matrix.det_diagonal,abs_mul,Finset.prod_inv_distrib,
      abs_inv,abs_of_pos hprod]
  calc
    _ = ENNReal.ofReal (∏ i, s i) *
        ENNReal.ofReal (((2 : ℝ)/(n : ℝ))^n * |A.det|) := by
      rw [← ENNReal.ofReal_mul hprod.le]
      congr 1
      rw [hdet]
      dsimp [V]
      field_simp [hprod.ne']
    _ ≤ ENNReal.ofReal (∏ i, s i) * volume K := mul_le_mul_right h _
    _ = _ := mul_comm _ _

end Kakeya4.Hard.MultilinearKakeya
