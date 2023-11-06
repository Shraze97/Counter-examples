import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology TopologicalSpace

universe u v w

structure DeletedIntegerSpace where
  x : ℝ
  hn : x > 0
  hx : ∀ y : ℕ , x ≠ y

notation "ℝ+" => DeletedIntegerSpace

def modified_Ioo(b : ℕ) : Set ℝ+ :=
  {a : ℝ+ | a.1 ∈ Set.Ioo (b : ℝ) (b+1 : ℝ )  }

def DIT_partition : Set (Set ℝ+) :=
  {S | ∃ (a : ℕ) , S = modified_Ioo a}

lemma pointfive_plus_x(x : ℕ) : ∀ y : ℕ , ((x: ℝ ) + 0.5 ) ≠ (y : ℝ) := by
  norm_num
  field_simp
  intros y h
  have : 1 = ((y : ℝ) - (x : ℝ)) * 2 := by
    linarith
  have b : ((y : ℝ) - (x : ℝ)) * 2 > 0 := by linarith
  apply Nat.not_even_one
  norm_cast at this
  rw[Nat.even_iff]
  zify
  rw[this]
  simp only [Int.mul_emod_left]

lemma x_plus_one_gt_zero(x : ℕ) : (x : ℝ) + 0.5 >  0 := by
  norm_num
  field_simp
  apply mul_pos
  have hx : (x*2 : ℝ) ≥  0 := by
    apply mul_nonneg
    norm_num
    norm_num
  linarith
  norm_num

lemma floor_cast_aux_2(r : ℝ+): Int.toNat ⌊r.x⌋ = Int.floor (r.x) := by
  rw[Int.toNat_of_nonneg]
  rw[Int.floor_nonneg]
  apply le_of_lt
  apply r.hn

lemma floor_cast_aux(r: ℝ+): @Nat.cast ℝ Real.natCast  (Int.toNat (Int.floor (r.x)))  =  Int.floor (r.x):= by
  norm_cast
  rw[floor_cast_aux_2 r]



theorem DIT_partition_is_partition : Setoid.IsPartition DIT_partition  := by
  rw[Setoid.IsPartition]
  constructor
  · rw[DIT_partition]
    simp only [mem_setOf_eq, not_exists]
    intro x
    apply Ne.symm
    rw[← Set.nonempty_iff_ne_empty,nonempty_def]
    set a : ℝ+ :=  {x := (x : ℝ)  + 0.5, hn := x_plus_one_gt_zero x , hx := pointfive_plus_x x} with ha
    use a
    rw[modified_Ioo]
    rw[mem_setOf_eq,Set.Ioo,mem_setOf_eq]
    constructor
    rw[ha]
    repeat (first | simp | norm_num)
  · intro r
    apply ExistsUnique.intro (modified_Ioo (Int.floor (r.x)).toNat)
    apply ExistsUnique.intro
    rw[modified_Ioo]
    simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, not_true, ge_iff_le, add_le_iff_nonpos_right, mem_Ioo,
      mem_setOf_eq]
    constructor
    norm_num
    rw[floor_cast_aux r,lt_iff_le_and_ne]
    constructor
    apply Int.floor_le
    intro ken
    apply r.hx
    rw[← ken,← floor_cast_aux r]
    rw[floor_cast_aux r]
    simp only [Int.lt_floor_add_one]
    swap
    have he' : modified_Ioo (Int.toNat ⌊r.x⌋) ∈ DIT_partition := by
      rw[DIT_partition]
      simp only [mem_setOf_eq]
      use Int.toNat ⌊r.x⌋
    apply he'
    intros he _
    simp only
    intros y ha
    match ha with
    | ⟨hy,hxa,hab ⟩ =>
    simp only at hxa
    simp only [implies_true] at hab
    rw[DIT_partition] at hy
    simp only [mem_setOf_eq] at hy
    match hy with
    |⟨ a, hay⟩ =>
    rw[hay,modified_Ioo] at hxa
    simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, not_true, ge_iff_le, add_le_iff_nonpos_right, mem_Ioo,
      mem_setOf_eq] at hxa
    norm_cast at hxa
    have hra : Int.toNat (Int.floor (r.x)) = a := by
      zify
      rw[floor_cast_aux_2 r]
      rw[Int.floor_eq_iff]
      norm_cast
      constructor
      exact le_of_lt hxa.1
      exact hxa.2
    rw[hra]
    assumption

def DeletedIntegerTopology_mk : TopologicalSpace ℝ+ :=
  TopologicalSpace.generateFrom DIT_partition

section DeletedIntegerTopology

variable [t : TopologicalSpace ℝ+](topology_eq : t = DeletedIntegerTopology_mk)



instance DIT_not_T0 : ¬ T0Space ℝ+ := by
  rw[t0Space_iff_inseparable]
  push_neg
  use {x := (1: ℝ ) + 0.5 , hn := by norm_num, hx := by sorry }
  use {x := (1: ℝ ) + 0.3 , hn := by norm_num, hx := by sorry }
  sorry
end DeletedIntegerTopology
