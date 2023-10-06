import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology    

universe u v w

def S (m : ℕ ) (H : Set (ℕ × ℕ) ) : Set ℕ :=
{ n : ℕ | (m,n) ∉ H }  

def AFSopen (H : Set (ℕ × ℕ)) : Prop :=
  (0,0) ∉ H ∨ ((0,0) ∈ H )

def ArensFortSpace_mk : TopologicalSpace (ℕ × ℕ) where 
IsOpen := 