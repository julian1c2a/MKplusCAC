/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import MKplusCAC.Relations

namespace MKplusCAC

open Classical

local infix:50 " ∈ᴹ " => Mem
local notation:50 x " ∉ᴹ " y:51 => ¬ Mem x y
local infix:50 " ⊆ᴹ " => SubClass
local notation "⟪" x ", " y "⟫" => opair x y
local infix:70 " ∩ᴹ " => inter
local infix:65 " ∪ᴹ " => union
local notation "𝐕ᴹ" => univ
local notation "∅ᴹ" => empty
local postfix:max "⁻¹" => inv

/-!
  # Functions
  Definitions and properties for class-functions, injections, surjections,
  bijections, and restrictions.
-/

-- ============================================================
-- Section 1: Operations for Classes (Functions)
-- ============================================================

-- Aplicación de una función a un argumento: F(x)
noncomputable def app (F x : Class) : Class :=
  if h : IsSet x ∧ ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F then
    Classical.choose h.2
  else
    Classical.choice inferInstance

local notation F " ⦑ " x " ⦒ " => app F x

-- Restricción de una función a una clase A
noncomputable def restrict (F A : Class) : Class :=
  {| p | ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ ⟪x, y⟫ ∈ᴹ F ∧ p = ⟪x, y⟫ |}

local infixl:80 " ↾ᴹ " => restrict

theorem mem_restrict_iff (F A p : Class) :
    p ∈ᴹ F ↾ᴹ A ↔ ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ ⟪x, y⟫ ∈ᴹ F ∧ p = ⟪x, y⟫ := by
  dsimp [restrict]
  rw [classComp_mem]
  constructor
  · rintro ⟨_, x, y, hx, hy, hxA, hF, rfl⟩
    exact ⟨x, y, hx, hy, hxA, hF, rfl⟩
  · rintro ⟨x, y, hx, hy, hxA, hF, rfl⟩
    exact ⟨isSet_opair hx hy, x, y, hx, hy, hxA, hF, rfl⟩

-- ============================================================
-- Section 2: Properties for Classes (Functions)
-- ============================================================

-- F es una función (como clase de pares).
def IsFun (F : Class) : Prop :=
  IsRel F ∧ IsClassFun F

-- F es una función con dominio A
def IsFunFrom (F A : Class) : Prop :=
  IsFun F ∧ dom F = A

-- F es una función de A en B
def IsFunFromTo (F A B : Class) : Prop :=
  IsFunFrom F A ∧ rng F ⊆ᴹ B

-- Función inyectiva (1-1)
def IsInjective (F : Class) : Prop :=
  IsFun F ∧ IsClassFun (F⁻¹)

-- Función sobreyectiva en B
def IsSurjective (F B : Class) : Prop :=
  rng F = B

-- Función biyectiva de A en B
def IsBijective (F A B : Class) : Prop :=
  IsFunFromTo F A B ∧ IsInjective F ∧ IsSurjective F B

-- ============================================================
-- Section 3: Advanced Theorems
-- ============================================================

theorem isFun_inv_of_injective (F : Class) (h : IsInjective F) : IsClassFun (F⁻¹) :=
  h.2

theorem isRel_restrict (F A : Class) : IsRel (F ↾ᴹ A) := by
  intro p hp
  obtain ⟨x, y, hx, hy, _, _, rfl⟩ := (mem_restrict_iff F A p).mp hp
  exact ⟨x, y, hx, hy, rfl⟩

theorem mem_restrict_iff' (F A p : Class) :
    p ∈ᴹ F ↾ᴹ A ↔ p ∈ᴹ F ∧ ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ p = ⟪x, y⟫ := by
  constructor
  · intro hp
    obtain ⟨x, y, hx, hy, hxA, hF, rfl⟩ := (mem_restrict_iff F A p).mp hp
    exact ⟨hF, x, y, hx, hy, hxA, rfl⟩
  · rintro ⟨hF, x, y, hx, hy, hxA, rfl⟩
    exact (mem_restrict_iff F A ⟪x, y⟫).mpr ⟨x, y, hx, hy, hxA, hF, rfl⟩

end MKplusCAC
