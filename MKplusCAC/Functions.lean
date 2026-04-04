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

-- F es una función con dominio contenido en A
def IsFunOn (F A : Class) : Prop :=
  IsFun F ∧ dom F ⊆ᴹ A

-- F es una función de A en B
def IsFunFromTo (F A B : Class) : Prop :=
  IsFunFrom F A ∧ rng F ⊆ᴹ B

-- F es invertible (su relación inversa es una función)
def IsInvertible (F : Class) : Prop :=
  IsClassFun (F⁻¹)

-- Función inyectiva (1-1)
def IsInjective (F : Class) : Prop :=
  IsFun F ∧ IsInvertible F

-- Función sobreyectiva en B
def IsSurjective (F B : Class) : Prop :=
  rng F = B

-- Función biyectiva de A en B
def IsBijective (F A B : Class) : Prop :=
  IsFunFromTo F A B ∧ IsInjective F ∧ IsSurjective F B

-- ============================================================
-- Section 3: Theorems for Classes (Functions)
-- ============================================================

theorem isClassFun_inv_of_injective (hF : IsInjective F) : IsClassFun (F⁻¹) :=
  hF.2

theorem isSet_app {F x : Class} (hcond : IsSet x ∧ ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F) : IsSet (F ⦑ x ⦒) := by
  dsimp [app]
  rw [dif_pos hcond]
  exact (Classical.choose_spec hcond.2).1

theorem mem_dom_of_app_defined {F x : Class} (hcond : IsSet x ∧ ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F) : x ∈ᴹ dom F := by
  rw [mem_dom_iff]
  exact ⟨hcond.1, Classical.choose_spec hcond.2⟩

theorem app_eq_of_eq (hF : IsFun F) {x y : Class} (hx : IsSet x) (hy : IsSet y) (hxy : x = y) :
    F ⦑ x ⦒ = F ⦑ y ⦒ := by
  dsimp [app]
  subst hxy
  by_cases h_split : (IsSet x ∧ ∃ z, IsSet z ∧ ⟪x, z⟫ ∈ᴹ F)
  · have h_split_y : (IsSet y ∧ ∃ z, IsSet z ∧ ⟪y, z⟫ ∈ᴹ F) := by rwa [← hxy]
    rw [dif_pos h_split, dif_pos h_split_y]
    let z₁ := Classical.choose h_split.2
    let z₂ := Classical.choose h_split_y.2
    have hz₁_spec := Classical.choose_spec h_split.2
    have hz₂_spec := Classical.choose_spec h_split_y.2
    rw [← hxy] at hz₁_spec
    exact hF.2 y z₁ z₂ hy hz₁.1 hz₂.1 hz₁_spec.2 hz₂_spec.2
  · have h_split_y_neg : ¬(IsSet y ∧ ∃ z, IsSet z ∧ ⟪y, z⟫ ∈ᴹ F) := by rwa [← hxy]
    rw [dif_neg h_split, dif_neg h_split_y_neg]

-- ============================================================
-- Section 4: Advanced Theorems
-- ============================================================

theorem isRel_restrict (F A : Class) : IsRel (F ↾ᴹ A) := by
  intro p hp
  obtain ⟨x, y, hx, hy, _, _, rfl⟩ := (mem_restrict_iff F A p).mp hp
  exact ⟨x, y, hx, hy, rfl⟩

theorem isFun_restrict (hF : IsFun F) (A : Class) : IsFun (F ↾ᴹ A) := by
  refine ⟨isRel_restrict F A, ?_⟩
  intro x y z hx hy hz h1 h2
  obtain ⟨_, _, _, _, _, hF1, rfl⟩ := (mem_restrict_iff F A ⟪x, y⟫).mp h1
  obtain ⟨_, _, _, _, _, hF2, rfl⟩ := (mem_restrict_iff F A ⟪x, z⟫).mp h2
  exact hF.2 x y z hx hy hz hF1 hF2

theorem isFunOn_restrict (hF : IsFunOn F B) (A : Class) : IsFunOn (F ↾ᴹ A) (A ∩ᴹ B) := by
  refine ⟨isFun_restrict hF.1 A, ?_⟩
  intro x hx_dom_restrict
  have hx_isSet := isSet_of_mem hx_dom_restrict
  rw [mem_dom_iff' hx_isSet] at hx_dom_restrict
  obtain ⟨y, h_xy_in_restrict⟩ := hx_dom_restrict
  obtain ⟨x', y', hx', hy', hxA, hF_mem, heq⟩ := (mem_restrict_iff F A ⟪x, y⟫).mp h_xy_in_restrict
  obtain ⟨rfl, rfl⟩ := opair_inj hx' hy' hx_isSet (isSet_app ⟨hx', ⟨y, hy', hF_mem⟩⟩) heq
  rw [mem_inter_iff' hx_isSet]
  constructor
  · exact hxA
  · apply hF.2
    rw [mem_dom_iff' hx_isSet]
    exact ⟨y, hF_mem⟩

theorem surjective_iff_forall_exists_app (hF : IsFun F) (B : Class) :
    IsSurjective F B ↔ ∀ y, y ∈ᴹ B → ∃ x, x ∈ᴹ dom F ∧ F ⦑ x ⦒ = y := by
  constructor
  · intro h_surj
    intro y hy_in_B
    have hy_in_rng : y ∈ᴹ rng F := by rw [h_surj]; exact hy_in_B
    rw [mem_rng_iff] at hy_in_rng
    obtain ⟨hy_set, x, hx_set, h_xy_in_F⟩ := hy_in_rng
    have hx_in_dom : x ∈ᴹ dom F := (mem_dom_iff' hx_set).mpr ⟨y, h_xy_in_F⟩
    use x, hx_in_dom
    dsimp [app]
    rw [dif_pos ⟨hx_set, ⟨y, hy_set, h_xy_in_F⟩⟩]
    let y' := Classical.choose ⟨y, hy_set, h_xy_in_F⟩
    have hy'_spec := Classical.choose_spec ⟨y, hy_set, h_xy_in_F⟩
    have h_xy'_in_F := hy'_spec.2
    exact (hF.2 x y' y hx_set hy'_spec.1 hy_set h_xy'_in_F h_xy_in_F).symm
  · intro h_forall
    apply subset_antisymm
    · intro y hy_in_rng
      rw [mem_rng_iff] at hy_in_rng
      obtain ⟨hy_set, x, hx_set, h_xy_in_F⟩ := hy_in_rng
      sorry -- Need to prove y ∈ B from here
    · intro y hy_in_B
      obtain ⟨x, hx_in_dom, h_app_eq_y⟩ := h_forall y hy_in_B
      rw [mem_rng_iff]
      sorry -- Need to prove ∃x, ⟪x,y⟫ ∈ F

theorem injective_iff_app_eq_imp_eq (F : Class) :
    IsInjective F ↔ IsFun F ∧ ∀ x₁ x₂ y₁ y₂,
      IsSet x₁ → IsSet x₂ → IsSet y₁ → IsSet y₂ →
      x₁ ∈ᴹ dom F → x₂ ∈ᴹ dom F →
      ⟪x₁, y₁⟫ ∈ᴹ F → ⟪x₂, y₂⟫ ∈ᴹ F →
      y₁ = y₂ → x₁ = x₂ := by
  constructor
  · rintro ⟨hFun, hInv⟩
    refine ⟨hFun, ?_⟩
    intro x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ _ _ hF₁ hF₂ hy
    subst hy
    have h_inv_mem₁ : ⟪y₁, x₁⟫ ∈ᴹ F⁻¹ := (mem_inv_iff F _).mpr ⟨x₁, y₁, hx₁, hy₁, hF₁, rfl⟩
    have h_inv_mem₂ : ⟪y₁, x₂⟫ ∈ᴹ F⁻¹ := (mem_inv_iff F _).mpr ⟨x₂, y₁, hx₂, hy₁, hF₂, rfl⟩
    exact hInv y₁ x₁ x₂ hy₁ hx₁ hx₂ h_inv_mem₁ h_inv_mem₂
  · rintro ⟨hFun, h_eq⟩
    refine ⟨hFun, ?_⟩
    intro y x₁ x₂ hy hx₁ hx₂ h_inv₁ h_inv₂
    obtain ⟨x₁', y₁', hx₁', hy₁', hF₁, heq₁⟩ := (mem_inv_iff F _).mp h_inv₁
    obtain ⟨x₂', y₂', hx₂', hy₂', hF₂, heq₂⟩ := (mem_inv_iff F _).mp h_inv₂
    obtain ⟨rfl, rfl⟩ := opair_inj hy hx₁ hy₁' hx₁' heq₁
    obtain ⟨rfl, rfl⟩ := opair_inj hy hx₂ hy₂' hx₂' heq₂
    apply h_eq x₁ x₂ y y hx₁ hx₂ hy hy
    · rw [mem_dom_iff' hx₁]; exact ⟨y, hF₁⟩
    · rw [mem_dom_iff' hx₂]; exact ⟨y, hF₂⟩
    · exact hF₁
    · exact hF₂
    · rfl

theorem mem_restrict_iff' (F A p : Class) :
    p ∈ᴹ F ↾ᴹ A ↔ p ∈ᴹ F ∧ ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ p = ⟪x, y⟫ := by
  constructor
  · intro hp
    obtain ⟨x, y, hx, hy, hxA, hF, rfl⟩ := (mem_restrict_iff F A p).mp hp
    exact ⟨hF, x, y, hx, hy, hxA, rfl⟩
  · rintro ⟨hF, x, y, hx, hy, hxA, rfl⟩
    exact (mem_restrict_iff F A ⟪x, y⟫).mpr ⟨x, y, hx, hy, hxA, hF, rfl⟩

end MKplusCAC
