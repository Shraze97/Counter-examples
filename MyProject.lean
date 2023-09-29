import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology    

universe u v w

def FiniteParticularPointTopology_mk{α : Type u}[Fintype α ](p : α ) : TopologicalSpace α  where
  IsOpen X:= p ∈ X ∨ X = ∅
  isOpen_univ := 
    by
      simp only [mem_univ, univ_eq_empty_iff, true_or]
  isOpen_inter := by
    intro s t hs ht
    simp only [mem_inter_iff]
    cases hs with
      | inl hp => 
        cases ht with
          | inl hq => 
            left
            exact ⟨hp,hq⟩
          | inr hq => 
            right
            rw [hq]
            simp only [inter_empty]
      | inr hp =>
        right
        rw [hp]
        simp only [empty_inter]
  isOpen_sUnion := by 
    intro S hS
    by_cases hSempty : ⋃₀S = ∅
    · simp only [hSempty, mem_empty_iff_false, or_true]
    · simp only [mem_sUnion,hSempty,exists_prop,or_false]
      push_neg at hSempty
      rw[← Set.nonempty_iff_ne_empty] at hSempty
      set x := hSempty.some with hxdef
      have hx : x ∈ ⋃₀S := Set.Nonempty.some_mem hSempty 
      rw[Set.mem_sUnion] at hx
      cases hx with 
        | intro t ht => 
          use t 
          have hnt : t.Nonempty := Set.nonempty_of_mem ht.2
          simp at hS
          exact ⟨ht.1, Or.resolve_right (hS t ht.1) (Set.nonempty_iff_ne_empty.mp hnt)⟩ 
          

section FiniteParticularPointTopology
variable (α : Type u)[f : Fintype α][t :TopologicalSpace α](p : α)(topology_eq : t = FiniteParticularPointTopology_mk p)

theorem FPT_open_iff {X : Set α} : IsOpen X ↔ p ∈ X ∨ X = ∅ := by
  rw [topology_eq]
  exact Iff.rfl

instance FPT_T₀ : T0Space α := by 
    rw[t0Space_iff_inseparable]
    intro x y hxy
    by_contra ha
    by_cases h : (x = p) ∨ (y = p); 
    · wlog hp : x = p
      apply this α p 
      apply topology_eq
      have hinsep : Inseparable y x:= Inseparable.symm hxy 
      apply hinsep
      apply Ne.symm ha
      exact h.symm 
      exact Or.resolve_left h hp
      rw[inseparable_iff_forall_open] at hxy
      let s : Set α := {p}
      have hsdef : s = {p} := by rfl
      have hs : IsOpen s := by
        rw[FPT_open_iff α p topology_eq ]
        left
        exact rfl 
      apply ha
      have hy : y ∈ s := by
        rwa[←hxy s hs] 
      rw [hsdef] at hy
      simp only [mem_singleton_iff] at hy  
      rw[hy,hp]
    · push_neg at h
      apply ha 
      rw[inseparable_iff_forall_open] at hxy
      let s : Set α := {p,x}
      have hsdef : s = {p,x} := by rfl
      have hs : IsOpen s := by
        rw[FPT_open_iff α p topology_eq]
        left
        simp only [mem_singleton_iff, mem_insert_iff, true_or]
      have hx : x ∈ s := by
        simp only [mem_singleton_iff, mem_insert_iff]
        right 
        trivial
      have hy : y ∈ s := by
        rwa[← hxy s hs ]
      rw [hsdef] at hy
      simp only [mem_singleton_iff, mem_insert_iff] at hy  
      exact (Or.resolve_left hy h.2).symm

end FiniteParticularPointTopology


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

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

#check eventually_of_forall
#check Eventually.mono
#check Eventually.and
