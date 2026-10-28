import OAI.MeasureTheory.Falconer.Incidence.LeafIncidenceGain
import OAI.MeasureTheory.Falconer.UniformProfileGain

/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Source: lean/OAI/MeasureTheory/Falconer/Incidence/LeafIncidenceGain.lean.
The proof is retained; the forall s,t is moved after all constant choices.
See the probe root COPYING and PROVENANCE.json. Pending fixed-environment validation.
-/

namespace OAI.Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem uniform_leaf_incidence_gain_all_parameters {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100)
    :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam ζ : ℝ, 0 < lam ∧ 0 < ζ ∧
    ∃ M : ℕ, 0 < M ∧ ∀ {s t : ℝ}, κ ≤ s → s ≤ 1-8*κ → s+8*κ ≤ t → ∀ m : ℕ, M ≤ m →
    ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 (m*B) → L.Nonempty →
      (∀ k ≤ m*B, ∀ q : CellPath 2,
        ((prefixFiber L k q).card:ℝ) ≤
          (2:ℝ)^((lam/4)*(m*B:ℕ))*(2:ℝ)^(-t*(k:ℝ))*(L.card:ℝ)) →
    ∀ Q : DyadicCube 2, Q.side = 1 →
    ∃ p ∈ L,
      let C := classLeaves L (blockLabel L (m*B) B (fun _ => []) (m+1))
        (blockLabel L (m*B) B (fun _ => []) (m+1) p);
      C.Nonempty ∧ (L.card:ℝ) ≤ (2:ℝ)^((lam/4)*(m*B:ℕ))*(C.card:ℝ) ∧
      ∀ a : ℝ, 0 < a → ∀ V : Space 2 → Finset (Space 2),
        QuarterPencilData (1/(2:ℝ)^(m*B+2)) s ((2:ℝ)^(lam*(m*B:ℕ))) a
          (quarterEndpointSet Q C 0 (m*B) []) V →
        (2:ℝ)^((s+ζ)*(m*B:ℕ)) ≤
          (((quarterEndpointSet Q C 0 (m*B) []).biUnion V).card:ℝ)/a := by
  obtain ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,hgain⟩ := uniform_profile_endpoint_gain_all_parameters hκ hκ1
  refine ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,?_⟩
  intro s t hs hs1 ht m hm L hL hLne hprefix Q hQ
  have hgain := hgain hs hs1 ht
  have hm0 : 0 < m := hM.trans_le hm
  let N := m*B
  let K := m+1
  have hK : N/B+1 = K := by dsimp [N,K]; rw [Nat.mul_div_cancel m hB]
  obtain ⟨hlabel,hprofile⟩ := hgain m hm L hL
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hsmall : (2:ℝ)^(lam/4*(N:ℝ)) ≤ (2:ℝ)^(lam*(N:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by linarith only [hlam] : lam/4 ≤ lam) hN0)
  have hbase : (2:ℝ)^K*((2*B+1:ℕ):ℝ)^K ≤ (2:ℝ)^(lam/4*(N:ℝ)) := by
    apply le_trans _ hlabel
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [K]
    omega
  have hcost : (2:ℝ)^(N/B+1)*((2*B+1:ℕ):ℝ)^(N/B+1)*
      (2:ℝ)^((lam/4)*(N:ℝ)) ≤ (2:ℝ)^(lam*(N:ℝ)) := by
    rw [hK]
    calc
      _ ≤ (2:ℝ)^((lam/4)*(N:ℝ))*(2:ℝ)^((lam/4)*(N:ℝ)) :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = (2:ℝ)^((lam/2)*(N:ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (by linarith only [hlam] : lam/2 ≤ lam) hN0)
  obtain ⟨p,hp,hmass,hcounts⟩ := exists_initial_profile_class hB hL hLne (by positivity) hprefix hcost
  rw [hK] at hmass hcounts
  let C := classLeaves L (blockLabel L N B (fun _ => []) K) (blockLabel L N B (fun _ => []) K p)
  have hpC : p ∈ C := by simp [C,classLeaves,hp]
  have hlabel' : ((2*B+1:ℕ):ℝ)^K ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
    apply le_trans _ hbase
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  refine ⟨p,hp,⟨p,hpC⟩,hmass.trans (mul_le_mul_of_nonneg_right hlabel' (Nat.cast_nonneg _)),?_⟩
  intro a ha V hV
  have hb := hprofile (fun _ => []) p Q hQ hcounts
  have hzero : blockDepth N B m = 0 := by simp [blockDepth,N]
  have hroot : blockDepth N B 0 = N := by simp [blockDepth]
  have hW : 1 ≤ (2:ℝ)^(lam*(N:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hsub : C ⊆ prefixFiber C 0 [] := by simp [prefixFiber_zero]
  have hmassSelf : ((prefixFiber C 0 []).card:ℝ) ≤ (2:ℝ)^(lam*(N:ℝ))*(C.card:ℝ) := by
    rw [prefixFiber_zero]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hW
  have hp0 : [] ∈ C.image (List.take (blockDepth N B m)) := by
    rw [hzero]
    exact Finset.mem_image.mpr ⟨p,hpC,by simp⟩
  have hv : QuarterPencilData (1/(2:ℝ)^(blockDepth N B 0-blockDepth N B m+2)) s
      ((2:ℝ)^(lam*(N:ℝ))) a (quarterEndpointSet Q C (blockDepth N B m) (blockDepth N B 0) []) V := by
    simpa only [hzero,hroot,Nat.sub_zero,N] using hV
  have hh := hb L (fun _ => []) p 0 [] hL hsub hmassSelf (Nat.zero_le _) [] hp0 a ha V hv
  simpa only [hzero,hroot,N] using hh

end OAI.Falconer
