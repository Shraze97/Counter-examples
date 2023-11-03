import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology TopologicalSpace

universe u v w


structure UpperHalfRationals where
  x : ℚ
  y : ℚ
  hy : 0 ≤  y


notation "ℚ+" => UpperHalfRationals


def B (ε : ℝ)(ζ : ℝ) : Set ℚ+ := {z : ℚ+ | ‖z.x - ζ‖ < ε ∧ z.y = 0}

def nhs_dit (θ : ℝ)(ε : ℝ)(z : ℚ+) : Set ℚ+ := {z} ∪ B ε (z.x - z.y / θ) ∪ B ε (z.x + z.y / θ)

lemma B_le (ε₁ : ℝ)(ε₂ : ℝ )(z : ℝ)(hε : ε₁ ≥  ε₂) : B ε₂ z ⊆ B ε₁ z :=
  by
    rw[B,B]
    simp only [Real.norm_eq_abs, setOf_subset_setOf, and_imp]
    intro x hx h
    apply And.intro
    · apply lt_of_lt_of_le hx
      assumption
    · assumption


lemma nhs_le (θ : ℝ)(ε₁ : ℝ)(ε₂ : ℝ )(z : ℚ+)(hε : ε₁ ≥  ε₂) : nhs_dit θ ε₂ z ⊆ nhs_dit θ ε₁ z := by
  rw[nhs_dit,nhs_dit]
  intro x hx
  simp only [singleton_union, mem_union, mem_insert_iff]
  simp only [singleton_union, mem_union, mem_insert_iff] at hx
  cases hx with
    | inl hl =>
      cases hl with
        | inl hll =>
          left
          left
          assumption
        | inr hlr =>
          left
          right
          apply B_le<;>
          assumption
    | inr hr  =>
      right
      apply B_le<;>
      assumption


def filter_gen (θ : ℝ)(z : ℚ+) : Filter ℚ+
    where
  sets := { t | ∃ ε : ℝ , t ⊇  nhs_dit θ ε z ∧ ε > 0}
  univ_sets := by
    simp only [gt_iff_lt, mem_setOf_eq, subset_univ, true_and]
    use 1
    simp only [zero_lt_one]
  sets_of_superset := by
    rintro x y hx hxy
    simp only [mem_setOf_eq] at hx
    simp only [mem_setOf_eq]
    match hx with
      | ⟨ε,hx,hε⟩ =>
        use ε
        constructor
        trans
        exact hxy
        exact hx
        assumption
  inter_sets := by
    rintro x y ⟨ε₁,hx⟩ ⟨ε₂,hy⟩
    use min ε₁ ε₂
    constructor
    apply subset_inter
    · trans
      apply nhs_le θ ε₁ (min ε₁ ε₂)
      simp only [ge_iff_le, min_le_iff, le_refl, true_or]
      exact hx.1
    · trans
      apply nhs_le θ ε₂ (min ε₁ ε₂)
      simp only [ge_iff_le, min_le_iff, le_refl, or_true]
      exact hy.1
    apply lt_min hx.2 hy.2


def DeletedIntegerTopology_mk (θ : ℝ)(hθ : Irrational θ) : TopologicalSpace ℚ+ :=
  TopologicalSpace.mkOfNhds (filter_gen θ)

lemma xaxisnhs (θ : ℝ)(ε : ℝ)(z : ℚ+)(hy : z.y = 0)(hε : ε > 0) : nhs_dit θ ε z = B ε z.x := by
  rw[nhs_dit]
  simp only [hy, Rat.cast_zero, zero_div, sub_zero, add_zero]
  have hz : z ∈ B ε z.x := by
    rw[B]
    simp
    constructor<;>
    assumption
  simp only [singleton_union, hz, insert_eq_of_mem, union_self]

lemma purenhsdit (θ : ℝ): pure ≤ filter_gen θ := by
  intros z n hnz
  simp only [mem_pure]
  rw[filter_gen] at hnz
  simp at hnz
  match hnz with
    | ⟨ε,hnε,hε⟩ =>
      apply Set.mem_of_subset_of_mem hnε
      rw[nhs_dit]
      simp only [singleton_union, mem_union, mem_insert_iff, true_or]

lemma nhs_dit_subs (θ : ℝ)(ε : ℝ)(p : ℝ)(a : ℚ+)(hay : a.y = 0)(hinq : |a.x - p| < ε ) : ∃ ε₂ : ℝ , nhs_dit θ ε₂ a ⊆ B ε p ∧ ε₂ > 0  := by
  sorry

theorem nhds_dit_filter_gen (θ : ℝ)(hθ : Irrational θ)(z : ℚ+) : @nhds ℚ+ (DeletedIntegerTopology_mk θ hθ) z = filter_gen θ z:= by
  apply nhds_mkOfNhds
  exact purenhsdit θ
  intros a s hs
  rw[filter_gen] at hs
  simp at hs
  match hs with
    | ⟨ε,hsε,hε⟩ =>
      set t := nhs_dit θ ε a with ht
      use t
      constructor
      rw[filter_gen]
      simp only [gt_iff_lt, Filter.mem_mk, mem_setOf_eq]
      use ε
      constructor
      assumption
      intros a' hat
      rw[filter_gen]
      simp only [gt_iff_lt, Filter.mem_mk, mem_setOf_eq]
      rw[ht,nhs_dit] at hat
      simp at hat
      cases hat with
      | inl hl =>
        cases hl with
        | inl hll =>
          rw[hll]

          sorry
        | inr hlr =>
          sorry
      | inr hr =>
        rw[B] at hr
        simp only [Real.norm_eq_abs, mem_setOf_eq] at hr
        have lem : ∃ ε₂ : ℝ , nhs_dit θ ε₂ a' ⊆ B ε (↑a.x + ↑a.y / θ) ∧ ε₂ > 0 := nhs_dit_subs θ ε (a.x + a.y / θ) a' hr.2 hr.1
        match lem with
          | ⟨ε₂,hε₂⟩ =>
            use ε₂
            constructor
            trans
            exact hsε
            rw[ht,nhs_dit]
            trans
            any_goals exact hε₂.1
            simp only [singleton_union, subset_union_right]
            exact hε₂.2






section DeletedIntegerTopology

variable (θ : ℝ)(hθ : Irrational θ)[t : TopologicalSpace ℚ+](topology_eq : t = DeletedIntegerTopology_mk θ hθ)

instance DIT_T2 : T2Space ℚ+ := by
  sorry


end DeletedIntegerTopology
