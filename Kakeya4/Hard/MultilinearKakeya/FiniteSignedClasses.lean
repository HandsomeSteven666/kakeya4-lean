import Kakeya4.Hard.MultilinearKakeya.AntipodalCover

/-! Closure separation for positive sign sets glued across finitely many
disjoint closed antipodal classes. Strict sign sets need not be closed. -/

noncomputable section
open Set
open scoped Topology Pointwise

namespace Kakeya4.Hard.MultilinearKakeya

def positiveClassUnion {m : ℕ} {ι : Type*} (C : ι → Set (UnitSphere m))
    (f : ι → UnitSphere m → ℝ) : Set (UnitSphere m) :=
  ⋃ i, C i ∩ {x | 0 < f i x}

theorem closure_positiveClassUnion_subset {m : ℕ} {ι : Type*} [Finite ι]
    (C : ι → Set (UnitSphere m)) (f : ι → UnitSphere m → ℝ)
    (hC : ∀ i, IsClosed (C i)) (hf : ∀ i, Continuous (f i)) :
    closure (positiveClassUnion C f) ⊆ ⋃ i, C i ∩ {x | 0 ≤ f i x} := by
  apply closure_minimal
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,hi.1,(show 0 < f i x from hi.2).le⟩
  · exact isClosed_iUnion_of_finite (fun i => (hC i).inter (isClosed_le continuous_const (hf i)))

theorem disjoint_positiveClassUnion_closure_neg {m : ℕ} {ι : Type*} [Finite ι]
    (C : ι → Set (UnitSphere m)) (f : ι → UnitSphere m → ℝ)
    (hC : ∀ i, IsClosed (C i)) (hf : ∀ i, Continuous (f i))
    (hneg : ∀ i x, -x ∈ C i ↔ x ∈ C i)
    (hodd : ∀ i x, f i (-x) = -f i x)
    (hd : Pairwise (fun i j => Disjoint (C i) (C j))) :
    Disjoint (positiveClassUnion C f) (closure (-positiveClassUnion C f)) := by
  apply Set.disjoint_left.mpr
  intro x hx hclosure
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  have hn : -x ∈ closure (positiveClassUnion C f) := by
    rw [← neg_closure] at hclosure
    exact Set.mem_neg.mp hclosure
  obtain ⟨j,hj⟩ := mem_iUnion.mp (closure_positiveClassUnion_subset C f hC hf hn)
  have hxj : x ∈ C j := (hneg j x).mp hj.1
  have hij : i = j := by
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) hi.1 hxj
  subst j
  have he := hodd i x
  have hi' : 0 < f i x := hi.2
  have hj' : 0 ≤ f i (-x) := hj.2
  linarith

end Kakeya4.Hard.MultilinearKakeya
