import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology

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
  sets := { t | ∃ ε  : ℝ , t ⊇  nhs_dit θ ε z}
  univ_sets := by
    simp only [mem_setOf_eq, subset_univ, exists_const]
  sets_of_superset := by
    rintro x y hx hxy
    simp only [mem_setOf_eq] at hx
    simp only [mem_setOf_eq]
    cases hx with
      | intro ε  hx =>
        use ε
        trans
        exact hxy
        exact hx
  inter_sets := by
    rintro x y ⟨ε₁,hx⟩ ⟨ε₂,hy⟩
    use min ε₁ ε₂
    apply subset_inter
    · trans
      apply nhs_le θ ε₁ (min ε₁ ε₂)
      simp only [ge_iff_le, min_le_iff, le_refl, true_or]
      assumption
    · trans
      apply nhs_le θ ε₂ (min ε₁ ε₂)
      simp only [ge_iff_le, min_le_iff, le_refl, or_true]
      assumption

def DeletedIntegerTopology_mk (θ : ℝ)(hθ : Irrational θ) : TopologicalSpace ℚ+ :=
  TopologicalSpace.mkOfNhds (filter_gen θ)
