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

def modified_T00(b : ℕ) : Set ℝ+ :=
  {a : ℝ+ | a.1 ∈ Set.Ioo (b : ℝ) (b+1 : ℝ )  }

def DIT_partition : Set (Set ℝ+) :=
  {S | ∃ (a : ℕ) , S = modified_T00 a}



theorem DIT_partition_is_partition : Setoid.IsPartition DIT_partition  := by
  rw[Setoid.IsPartition]
  constructor
  · rw[DIT_partition]
    simp only [mem_setOf_eq, not_exists]
    intro x
    apply Ne.symm
    rw[← Set.nonempty_iff_ne_empty,nonempty_def]
    have hpointfive : ∀ y : ℕ , ((x: ℝ ) + 0.5 ) ≠ (y : ℝ) := by
      norm_num
      field_simp
      intro y
      intro h
      have : 1 = ((y : ℝ) - (x : ℝ)) * 2 := by
        linarith
      have b : ((y : ℝ) - (x : ℝ)) * 2 > 0 := by linarith
      apply Nat.not_even_one
      norm_cast at this
      rw[Nat.even_iff]
      zify
      rw[this]
      simp only [Int.mul_emod_left]
    have hx0 : (x : ℝ) + 0.5 >  0 := by
      norm_num
      field_simp
      apply mul_pos
      have hx : (x*2 : ℝ) ≥  0 := by
        apply mul_nonneg
        norm_num
        norm_num
      linarith
      norm_num
    set a : ℝ+ :=  {x := (x : ℝ)  + 0.5, hn := hx0 , hx := hpointfive} with ha
    use a
    rw[modified_T00]
    rw[mem_setOf_eq,Set.Ioo,mem_setOf_eq]
    constructor
    rw[ha]
    repeat (first | simp | norm_num)
  · intro r
    apply ExistsUnique.intro (modified_T00 (Int.floor (r.x)).toNat)
    apply ExistsUnique.intro
    rw[modified_T00]
    simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, not_true, ge_iff_le, add_le_iff_nonpos_right, mem_Ioo,
      mem_setOf_eq]
    constructor
    norm_num
    sorry
    sorry
    sorry
    sorry
    sorry
