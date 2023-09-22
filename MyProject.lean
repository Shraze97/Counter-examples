import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology

universe u v w

instance ParticularPointTopology : TopologicalSpace Prop :=
  sorry
theorem my_lemma :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by 
      rw [abs_mul]
    _ ≤ |x| * ε := by 
      apply mul_le_mul
      sorry
      sorry
      sorry
      sorry
    _ < 1 * ε := sorry
    _ = ε := sorry

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

variable (f : ℝ → ℝ)

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := 
  by
    dsimp [sets]
    simp[subset_univ]
  sets_of_superset := by
    intro x y hs hxy
    dsimp [sets] at *
    trans x <;>
    assumption
  inter_sets := by
    intro s t hs ht
    rename_i x 
    dsimp [sets] at hs ht
    apply subset_inter_iff.mpr
    exact ⟨hs,ht⟩

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      dsimp [sets]
      use 0
      intro b hb
      simp 
    sets_of_superset := 
    by
      intro x y hx hxy
      dsimp [sets] at *
      cases hx 
      rename_i a ha
      use a 
      intro b hb
      apply hxy
      exact ha b hb
    inter_sets := by
      intro s t hs ht
      dsimp[sets] at *
      cases hs with 
      | intro a ha => 
      cases ht with
      | intro c hc =>
      use max a c 
      intro b hb
      simp only [mem_inter_iff]
      constructor
      apply ha 
      exact (max_le_iff.mp hb).1
      apply hc
      exact (max_le_iff.mp hb).2 }


def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

#check @Filter.comap
#check @Filter.map_le_iff_le_comap
#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
  intro V hV
  dsimp [Tendsto₁] at *
  rw [preimage_comp]
  apply hf 
  apply hg
  assumption

variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)


#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
  rw [nhds_prod_eq]
  simp only [Tendsto]
  dsimp only [SProd.sprod,Filter.prod]
  rw[le_inf_iff,←Filter.map_le_iff_le_comap,←Filter.map_le_iff_le_comap,map_map,map_map]

example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp
