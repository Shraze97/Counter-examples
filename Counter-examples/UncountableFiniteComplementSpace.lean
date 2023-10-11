import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology    

universe u v w

def UFCS_mk {α : Type u}(hα : ¬ (Countable α ) ) : TopologicalSpace α where
  IsOpen X := Set.Finite Xᶜ ∨ X = ∅ 
  isOpen_univ := by 
    simp only [compl_univ, finite_empty, univ_eq_empty_iff, true_or]
  isOpen_inter := by
    simp only
    intro s t hs ht
    rw[Set.compl_inter]
    cases hs with
      | inl hsf => 
        cases ht with
          | inl htf => 
            left
            apply   Set.finite_union.mpr 
            exact ⟨hsf,htf⟩
          | inr htn =>
            right 
            rw[htn]
            simp only [inter_empty]
      | inr hsn =>
        right
        rw[hsn]
        simp only [empty_inter]
        
  isOpen_sUnion := by 
    simp only
    intro s hs
    by_cases h : ⋃₀ s = ∅;
    · right 
      exact h
    left
    push_neg at h
    rw[← Set.nonempty_iff_ne_empty] at h
    set x := h.some with hxdef
    have hx : x ∈ ⋃₀ s := Set.Nonempty.some_mem h
    rw[Set.mem_sUnion] at hx
    cases hx with 
      | intro t ht => 
        have htf : Set.Finite tᶜ := by 
          have htn : t ≠ ∅ := by  
            by_contra ht0
            rw[ht0] at ht
            simp at ht
          exact Or.resolve_right (hs t ht.1) htn
        apply Set.Finite.subset htf  
        rw[Set.compl_subset_compl]
        intro x hx 
        rw[Set.mem_sUnion]
        use t 
        exact ⟨ht.1, hx⟩

section UncountableFiniteComplementSpace 
variable (α : Type u)[t : TopologicalSpace α](hα : ¬ (Countable α )) (topology_eq : t = UFCS_mk hα)

theorem UFCS_open_iff{X : Set α} : IsOpen X ↔ Set.Finite Xᶜ ∨ X = ∅ := by
  rw[topology_eq]
  exact Iff.rfl

instance UFCS_T₁ : T1Space α := by 
  rw [t1Space_iff_exists_open]
  intro x y hxy
  set U : Set α := {y}ᶜ with hU 
  have hUopen : IsOpen U := by 
    rw[UFCS_open_iff α hα topology_eq]
    left 
    rw[hU]
    simp only [compl_compl, finite_singleton]
  have hx : x ∈ U := by 
    rw[hU]
    simp only [mem_compl_iff, mem_singleton_iff]
    exact hxy
  have hy : y ∉ U := by
    simp only [mem_compl_iff, mem_singleton_iff, not_true, not_false_eq_true]
  exact ⟨U, hUopen, hx, hy⟩
    