/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import MKplusCAC.MKplusCACAxioms

namespace MKplusCAC

local infix:50 " ∈ᴹ " => Mem
local notation:50 x " ∉ᴹ " y:51 => ¬ Mem x y
local infix:50 " ⊆ᴹ " => SubClass
local notation "⟪" x ", " y "⟫" => opair x y
local infix:70 " ∩ᴹ " => inter
local infix:65 " ∪ᴹ " => union
local notation "𝐕ᴹ" => univ
local notation "∅ᴹ" => empty

/-!
  # Relations
  Definitions and properties for relations, domain, range,
  Cartesian product, composition, and inverses.
-/

-- ============================================================
-- Section 1: Operations for Classes
-- ============================================================

-- Cartesian Product
noncomputable def prod (A B : Class) : Class :=
  {| p | ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ y ∈ᴹ B ∧ p = ⟪x, y⟫ |}

local infix:70 " ×ᴹ " => prod

theorem mem_prod_iff (A B p : Class) :
    p ∈ᴹ A ×ᴹ B ↔ ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ y ∈ᴹ B ∧ p = ⟪x, y⟫ := by
  dsimp [prod]
  rw [classComp_mem]
  constructor
  · rintro ⟨_, x, y, hx, hy, hxA, hyB, rfl⟩
    exact ⟨x, y, hx, hy, hxA, hyB, rfl⟩
  · rintro ⟨x, y, hx, hy, hxA, hyB, rfl⟩
    exact ⟨isSet_opair hx hy, x, y, hx, hy, hxA, hyB, rfl⟩

-- Rango de una clase (relación)
noncomputable def rng (R : Class) : Class :=
  {| y | ∃ x, IsSet x ∧ ⟪x, y⟫ ∈ᴹ R |}

theorem mem_rng_iff (R y : Class) :
    y ∈ᴹ rng R ↔ IsSet y ∧ ∃ x, IsSet x ∧ ⟪x, y⟫ ∈ᴹ R :=
  classComp_mem _ y

-- Relación inversa
noncomputable def inv (R : Class) : Class :=
  {| p | ∃ x y, IsSet x ∧ IsSet y ∧ ⟪x, y⟫ ∈ᴹ R ∧ p = ⟪y, x⟫ |}

local postfix:max "⁻¹" => inv

theorem mem_inv_iff (R p : Class) :
    p ∈ᴹ R⁻¹ ↔ ∃ x y, IsSet x ∧ IsSet y ∧ ⟪x, y⟫ ∈ᴹ R ∧ p = ⟪y, x⟫ := by
  dsimp [inv]
  rw [classComp_mem]
  constructor
  · rintro ⟨_, x, y, hx, hy, hR, rfl⟩
    exact ⟨x, y, hx, hy, hR, rfl⟩
  · rintro ⟨x, y, hx, hy, hR, rfl⟩
    exact ⟨isSet_opair hy hx, x, y, hx, hy, hR, rfl⟩

-- Composición de relaciones (S ∘ R : (x, z) ∈ S ∘ R iff ∃ y, (x, y) ∈ R ∧ (y, z) ∈ S)
noncomputable def comp (S R : Class) : Class :=
  {| p | ∃ x y z, IsSet x ∧ IsSet y ∧ IsSet z ∧ ⟪x, y⟫ ∈ᴹ R ∧ ⟪y, z⟫ ∈ᴹ S ∧ p = ⟪x, z⟫ |}

local infixl:80 " ∘ᴹ " => comp

theorem mem_comp_iff (S R p : Class) :
    p ∈ᴹ S ∘ᴹ R ↔ ∃ x y z, IsSet x ∧ IsSet y ∧ IsSet z ∧ ⟪x, y⟫ ∈ᴹ R ∧ ⟪y, z⟫ ∈ᴹ S ∧ p = ⟪x, z⟫ := by
  dsimp [comp]
  rw [classComp_mem]
  constructor
  · rintro ⟨_, x, y, z, hx, hy, hz, hR, hS, rfl⟩
    exact ⟨x, y, z, hx, hy, hz, hR, hS, rfl⟩
  · rintro ⟨x, y, z, hx, hy, hz, hR, hS, rfl⟩
    exact ⟨isSet_opair hx hz, x, y, z, hx, hy, hz, hR, hS, rfl⟩

-- ============================================================
-- Section 2: Properties for Classes
-- ============================================================

-- R es una relación (todos sus elementos son pares ordenados)
def IsRel (R : Class) : Prop :=
  ∀ p : Class, p ∈ᴹ R → ∃ x y, IsSet x ∧ IsSet y ∧ p = ⟪x, y⟫

-- Relación reflexiva en A
def ReflexiveOn (R A : Class) : Prop :=
  IsRel R ∧ (∀ x : Class, IsSet x → x ∈ᴹ A → ⟪x, x⟫ ∈ᴹ R)

-- Relación simétrica
def Symmetric (R : Class) : Prop :=
  IsRel R ∧ (∀ x y : Class, IsSet x → IsSet y → ⟪x, y⟫ ∈ᴹ R → ⟪y, x⟫ ∈ᴹ R)

-- Relación transitiva
def Transitive (R : Class) : Prop :=
  IsRel R ∧ (∀ x y z : Class, IsSet x → IsSet y → IsSet z →
    ⟪x, y⟫ ∈ᴹ R → ⟪y, z⟫ ∈ᴹ R → ⟪x, z⟫ ∈ᴹ R)

-- Relación de equivalencia en A
def EquivalenceOn (R A : Class) : Prop :=
  ReflexiveOn R A ∧ Symmetric R ∧ Transitive R

-- Antisimetría
def Antisymmetric (R : Class) : Prop :=
  IsRel R ∧ (∀ x y : Class, IsSet x → IsSet y →
    ⟪x, y⟫ ∈ᴹ R → ⟪y, x⟫ ∈ᴹ R → x = y)

-- Preorden en A
def PreorderOn (R A : Class) : Prop :=
  ReflexiveOn R A ∧ Transitive R

-- Orden parcial en A
def PartialOrderOn (R A : Class) : Prop :=
  PreorderOn R A ∧ Antisymmetric R

-- Orden total (lineal) en A
def TotalOrderOn (R A : Class) : Prop :=
  PartialOrderOn R A ∧
  (∀ x y : Class, IsSet x → IsSet y → x ∈ᴹ A → y ∈ᴹ A →
    ⟪x, y⟫ ∈ᴹ R ∨ ⟪y, x⟫ ∈ᴹ R)

-- Irreflexividad en A
def IrreflexiveOn (R A : Class) : Prop :=
  IsRel R ∧ (∀ x : Class, IsSet x → x ∈ᴹ A → ⟪x, x⟫ ∉ᴹ R)

-- Orden estricto parcial en A
def StrictPartialOrderOn (R A : Class) : Prop :=
  IrreflexiveOn R A ∧ Transitive R

-- Orden estricto total en A
def StrictTotalOrderOn (R A : Class) : Prop :=
  StrictPartialOrderOn R A ∧
  (∀ x y : Class, IsSet x → IsSet y → x ∈ᴹ A → y ∈ᴹ A → x ≠ y →
    ⟪x, y⟫ ∈ᴹ R ∨ ⟪y, x⟫ ∈ᴹ R)

-- ============================================================
-- Section 3: Advanced Theorems (Algebraic Properties)
-- ============================================================

theorem inv_inv (R : Class) : (R⁻¹)⁻¹ = R ∩ᴹ (𝐕ᴹ ×ᴹ 𝐕ᴹ) := by
  apply MK_Ext; intro p _
  constructor
  · intro hp
    obtain ⟨y, x, hy, hx, hRinv, rfl⟩ := (mem_inv_iff _ _).mp hp
    obtain ⟨x', y', hx', hy', hR, heq⟩ := (mem_inv_iff _ _).mp hRinv
    obtain ⟨rfl, rfl⟩ := opair_inj hy hx hy' hx' heq
    rw [mem_inter_iff' (isSet_opair hx hy)]
    refine ⟨hR, ?_⟩
    rw [mem_prod_iff]
    exact ⟨x, y, hx, hy, isSet_iff_mem_univ.mp hx, isSet_iff_mem_univ.mp hy, rfl⟩
  · intro hp
    rw [mem_inter_iff' (isSet_of_mem hp)] at hp
    obtain ⟨hpR, hpProd⟩ := hp
    obtain ⟨x, y, hx, hy, _, _, rfl⟩ := (mem_prod_iff _ _ _).mp hpProd
    rw [mem_inv_iff]
    exact ⟨y, x, hy, hx, (mem_inv_iff R ⟪y, x⟫).mpr ⟨x, y, hx, hy, hpR, rfl⟩, rfl⟩

theorem inv_comp (S R : Class) : (S ∘ᴹ R)⁻¹ = R⁻¹ ∘ᴹ S⁻¹ := by
  apply MK_Ext; intro p _
  constructor
  · intro hpInv
    obtain ⟨x, z, hx, hz, hSR, rfl⟩ := (mem_inv_iff _ _).mp hpInv
    obtain ⟨x', y, z', hx', hy, hz', hR, hS, heq⟩ := (mem_comp_iff _ _ _).mp hSR
    obtain ⟨rfl, rfl⟩ := opair_inj hx hz hx' hz' heq
    rw [mem_comp_iff]
    exact ⟨z, y, x, hz, hy, hx,
      (mem_inv_iff S _).mpr ⟨y, z, hy, hz, hS, rfl⟩,
      (mem_inv_iff R _).mpr ⟨x, y, hx, hy, hR, rfl⟩, rfl⟩
  · intro hpComp
    obtain ⟨z, y, x, hz, hy, hx, hSinv, hRinv, rfl⟩ := (mem_comp_iff _ _ _).mp hpComp
    obtain ⟨y', z', hy', hz', hS, heqS⟩ := (mem_inv_iff S ⟪z, y⟫).mp hSinv
    obtain ⟨x', y'', hx', hy'', hR, heqR⟩ := (mem_inv_iff R ⟪y, x⟫).mp hRinv
    obtain ⟨rfl, rfl⟩ := opair_inj hz hy hz' hy' heqS
    obtain ⟨rfl, rfl⟩ := opair_inj hy hx hy'' hx' heqR
    rw [mem_inv_iff]
    exact ⟨x, z, hx, hz, (mem_comp_iff S R ⟪x, z⟫).mpr ⟨x, y, z, hx, hy, hz, hR, hS, rfl⟩, rfl⟩

theorem comp_assoc (T S R : Class) : (T ∘ᴹ S) ∘ᴹ R = T ∘ᴹ (S ∘ᴹ R) := by
  apply MK_Ext; intro p _
  constructor
  · intro hp
    obtain ⟨x, y, w, hx, hy, hw, hR, hTS, rfl⟩ := (mem_comp_iff _ _ _).mp hp
    obtain ⟨y', z, w', hy', hz, hw', hS, hT, heq⟩ := (mem_comp_iff _ _ _).mp hTS
    obtain ⟨rfl, rfl⟩ := opair_inj hy hw hy' hw' heq
    rw [mem_comp_iff]
    exact ⟨x, z, w, hx, hz, hw, (mem_comp_iff S R ⟪x, z⟫).mpr ⟨x, y, z, hx, hy, hz, hR, hS, rfl⟩, hT, rfl⟩
  · intro hp
    obtain ⟨x, z, w, hx, hz, hw, hSR, hT, rfl⟩ := (mem_comp_iff _ _ _).mp hp
    obtain ⟨x', y, z', hx', hy, hz', hR, hS, heq⟩ := (mem_comp_iff _ _ _).mp hSR
    obtain ⟨rfl, rfl⟩ := opair_inj hx hz hx' hz' heq
    rw [mem_comp_iff]
    exact ⟨x, y, w, hx, hy, hw, hR, (mem_comp_iff T S ⟪y, w⟫).mpr ⟨y, z, w, hy, hz, hw, hS, hT, rfl⟩, rfl⟩

end MKplusCAC
