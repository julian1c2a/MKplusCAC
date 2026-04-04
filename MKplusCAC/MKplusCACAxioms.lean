/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  MK⁺ — Morse-Kelley Set Theory + Class Axiom Scheme of Choice
  =============================================================

  Parallel development to ZfcSetTheory (ZFC), but grounded on a
  two-sorted ontology:

    · Sets    — collections that *belong to* some class.
    · Classes — any definable collection (sets are a subclass).

  Key differences from ZFC / ZfcSetTheory:
    1. Proper classes are first-class objects (not just informal talk).
    2. Comprehension schema (A7) allows formulas quantifying over classes,
       not just over sets — making MK strictly stronger than ZFC.
    3. Global Choice is included as A9 in the base MK axioms,
       following Kelley (1955). This is already stronger than AC in ZFC.
    4. MK⁺ = MK (with Global Choice) + Class Axiom Scheme of Choice (CAC).
       CAC is strictly stronger than Global Choice over MK.

  Lean encoding strategy:
    · A single Lean `Type` called `Class` for the universe of discourse.
    · `Mem : Class → Class → Prop` as the primitive membership relation.
    · `IsSet : Class → Prop` defined from membership (see §1).
    · Ordered pairs ⟪x, y⟫ are a *defined* notion (Kuratowski or Morse).
    · All axioms are stated as `axiom` declarations — left `sorry`-free
      by design; concrete proofs will live in separate modules.
-/

import MKplusCAC.Prelim
-- Available from Prelim (no re-import needed):
--   ExistsUnique, ∃! x, p, ∃¹ x, p
--   ExistsUnique.intro / .exists / .choose / .choose_spec / .unique
--   choose_unique / choose_spec_unique / choose_uniq  (Peano-compatible)
--   Classical.*   (via open Classical in Prelim)

namespace MKplusCAC

open Classical

/-! ─────────────────────────────────────────────────────────────────────────
    §0 · Primitive Sorts and Relations
    ─────────────────────────────────────────────────────────────────────────

  We postulate:
    · `Class`   — the universe of all classes (a Lean `Type`).
    · `Mem`     — the binary membership relation on classes.

  Everything else (IsSet, pairs, union, etc.) is *defined* from these.
-/

-- The universe of all classes (both sets and proper classes).
axiom Class : Type

-- Primitive membership.
axiom Mem : Class → Class → Prop

-- Preferred infix notation for membership.
local infix:50 " ∈ᴹ " => Mem
local notation:50 x " ∉ᴹ " y:51 => ¬ Mem x y


/-! ─────────────────────────────────────────────────────────────────────────
    §1 · Defined Notions (sin axiomas)
    ─────────────────────────────────────────────────────────────────────────

  These are purely definitional; they carry no axiomatic content.
-/

-- A class X is a *set* iff it is a member of some class Y.
def IsSet (X : Class) : Prop := ∃ Y : Class, X ∈ᴹ Y

-- X is a subclass of Y (class inclusion).
def SubClass (X Y : Class) : Prop := ∀ u : Class, (u ∈ᴹ X) → (u ∈ᴹ Y)
local infix:50 " ⊆ᴹ " => SubClass

-- Todo miembro de una clase es un set (directo de la definición de IsSet).
theorem mem_isSet {u X : Class} (h : u ∈ᴹ X) : IsSet u := ⟨X, h⟩


/-! ─────────────────────────────────────────────────────────────────────────
    §2 · Axioms of Morse-Kelley Set Theory (MK)
    ─────────────────────────────────────────────────────────────────────────

  Standard presentation following:
    · J.L. Kelley, "General Topology" (1955), Appendix.
    · A.P. Morse, "A Theory of Sets" (1965).
    · E. Mendelson, "Introduction to Mathematical Logic", Ch. 4.

  The eight axioms below constitute MK proper.
  (MK⁺ adds the class choice axioms in §3.)
-/

-- ── A1. Extensionality ────────────────────────────────────────────────────
-- Two classes with the same set-members are identical.
-- Note: membership is only tested on *sets* (not arbitrary classes).
axiom MK_Ext :
  ∀ X Y : Class,
    (∀ u : Class, IsSet u → (u ∈ᴹ X ↔ u ∈ᴹ Y)) → X = Y

-- ── A2. Foundation (Regularity) ───────────────────────────────────────────
-- Every non-empty class has an ∈ᴹ-minimal member.
-- Equivalently: no class is a member of itself, and ∈ᴹ is well-founded on sets.
axiom MK_Found :
  ∀ X : Class, (∃ u : Class, u ∈ᴹ X) →
    ∃ u : Class, u ∈ᴹ X ∧ ¬ ∃ v : Class, v ∈ᴹ u ∧ v ∈ᴹ X

-- ── A3. Pairing ───────────────────────────────────────────────────────────
-- For any two sets x, y their unordered pair {x, y} is a set.
axiom MK_Pair :
  ∀ x y : Class, IsSet x → IsSet y →
    ∃ z : Class, IsSet z ∧ ∀ u : Class, (u ∈ᴹ z) ↔ ((u = x) ∨ (u = y))

/-! ─────────────────────────────────────────────────────────────────────────
    §1b · Pares y singletons (requieren A3)
    ─────────────────────────────────────────────────────────────────────────
-/

-- Par no ordenado {x, y}: testigo de A3.
noncomputable def UPair (x y : Class) (hx : IsSet x) (hy : IsSet y) : Class :=
  Classical.choose (MK_Pair x y hx hy)

theorem UPair_isSet {x y : Class} (hx : IsSet x) (hy : IsSet y) :
    IsSet (UPair x y hx hy) :=
  (Classical.choose_spec (MK_Pair x y hx hy)).1

theorem UPair_mem {x y : Class} (hx : IsSet x) (hy : IsSet y) (u : Class) :
    (u ∈ᴹ UPair x y hx hy) ↔ (u = x ∨ u = y) :=
  (Classical.choose_spec (MK_Pair x y hx hy)).2 u

-- Singleton {x} := {x, x}.
noncomputable def Sing (x : Class) (hx : IsSet x) : Class := UPair x x hx hx

theorem Sing_isSet {x : Class} (hx : IsSet x) : IsSet (Sing x hx) :=
  UPair_isSet hx hx

theorem Sing_mem {x : Class} (hx : IsSet x) (u : Class) :
    (u ∈ᴹ Sing x hx) ↔ (u = x) := by
  simp [Sing, UPair_mem hx hx]

-- Singleton es inyectivo.
theorem Sing_inj {x x' : Class} (hx : IsSet x) (hx' : IsSet x')
    (h : Sing x hx = Sing x' hx') : x = x' :=
  (Sing_mem hx' x).mp (h ▸ (Sing_mem hx x).mpr rfl)

-- Igualdad de pares no ordenados implica igualdad de componentes (en algún orden).
theorem UPair_cases {x y x' y' : Class} (hx : IsSet x) (hy : IsSet y)
    (hx' : IsSet x') (hy' : IsSet y')
    (h : UPair x y hx hy = UPair x' y' hx' hy') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  -- Extraemos presencia de x e y en el par derecho
  have hx_in := (UPair_mem hx' hy' x).mp (h ▸ (UPair_mem hx hy x).mpr (Or.inl rfl))
  have hy_in := (UPair_mem hx' hy' y).mp (h ▸ (UPair_mem hx hy y).mpr (Or.inr rfl))
  rcases hx_in with hxx' | hxy'
  · -- x = x'
    rcases hy_in with hyx' | hyy'
    · -- y = x'; determinamos y' desde el par izquierdo
      have hy'_in := (UPair_mem hx hy y').mp
        (h.symm ▸ (UPair_mem hx' hy' y').mpr (Or.inr rfl))
      rcases hy'_in with hy'x | hy'y
      · exact Or.inl ⟨hxx', hyx'.trans (hxx'.symm.trans hy'x.symm)⟩
      · exact Or.inl ⟨hxx', hy'y.symm⟩
    · exact Or.inl ⟨hxx', hyy'⟩
  · -- x = y'
    rcases hy_in with hyx' | hyy'
    · exact Or.inr ⟨hxy', hyx'⟩
    · -- x = y', y = y'; determinamos x' desde el par izquierdo
      have hx'_in := (UPair_mem hx hy x').mp
        (h.symm ▸ (UPair_mem hx' hy' x').mpr (Or.inl rfl))
      rcases hx'_in with hx'x | hx'y
      · exact Or.inl ⟨hx'x.symm, hyy'⟩
      · exact Or.inr ⟨hxy', hx'y.symm⟩

-- Par de Kuratowski: ⟪x, y⟫ := {{x}, {x, y}}.
noncomputable def OPair (x y : Class) (hx : IsSet x) (hy : IsSet y) : Class :=
  UPair (Sing x hx) (UPair x y hx hy) (Sing_isSet hx) (UPair_isSet hx hy)

-- Inyectividad del par de Kuratowski.
theorem OPair_inj {x y x' y' : Class} (hx : IsSet x) (hy : IsSet y)
    (hx' : IsSet x') (hy' : IsSet y')
    (h : OPair x y hx hy = OPair x' y' hx' hy') : x = x' ∧ y = y' := by
  rcases UPair_cases (Sing_isSet hx) (UPair_isSet hx hy)
                     (Sing_isSet hx') (UPair_isSet hx' hy') h with
    ⟨hSS', hPP'⟩ | ⟨hSP', hPS'⟩
  · -- Sing x = Sing x'  ∧  UPair x y = UPair x' y'
    have hxx' := Sing_inj hx hx' hSS'
    rcases UPair_cases hx hy hx' hy' hPP' with ⟨_, hyy'⟩ | ⟨hxy', hyx'⟩
    · exact ⟨hxx', hyy'⟩
    · -- x = y', y = x'; con x = x': y = x' = x = y'
      exact ⟨hxx', hyx'.trans (hxx'.symm.trans hxy')⟩
  · -- Sing x = UPair x' y'  ∧  UPair x y = Sing x'
    have hx'x : x' = x := by
      have h1 : x' ∈ᴹ UPair x' y' hx' hy' := (UPair_mem hx' hy' x').mpr (Or.inl rfl)
      rw [← hSP'] at h1; exact (Sing_mem hx x').mp h1
    have hy'x : y' = x := by
      have h1 : y' ∈ᴹ UPair x' y' hx' hy' := (UPair_mem hx' hy' y').mpr (Or.inr rfl)
      rw [← hSP'] at h1; exact (Sing_mem hx y').mp h1
    have hyx' : y = x' := by
      have h1 : y ∈ᴹ UPair x y hx hy := (UPair_mem hx hy y).mpr (Or.inr rfl)
      rw [hPS'] at h1; exact (Sing_mem hx' y).mp h1
    -- x = x' y y = y' (via y = x' = x = y')
    exact ⟨hx'x.symm, hyx'.trans (hx'x.trans hy'x.symm)⟩

-- ── A4. Union ─────────────────────────────────────────────────────────────
-- The union ⋃x of a set x is a set.
axiom MK_Union :
  ∀ x : Class, IsSet x →
    ∃ z : Class, IsSet z ∧
      ∀ u : Class, u ∈ᴹ z ↔ ∃ v : Class, u ∈ᴹ v ∧ v ∈ᴹ x

-- ── A5. Power Set ─────────────────────────────────────────────────────────
-- The power class 𝒫(x) = {u | u ⊆ x} of a set x is a set.
axiom MK_Pow :
  ∀ x : Class, IsSet x →
    ∃ z : Class, IsSet z ∧
      ∀ u : Class, u ∈ᴹ z ↔ IsSet u ∧ ∀ v : Class, v ∈ᴹ u → v ∈ᴹ x

-- ── A6. Infinity ──────────────────────────────────────────────────────────
-- There exists an inductive set: one containing ∅ and closed under
-- the von Neumann successor s(x) = x ∪ {x}.
-- (∅ and s are defined via A3 + A4 + A7; stated here informally.)
axiom MK_Inf :
  ∃ x : Class, IsSet x ∧
    -- ∅ ∈ x:
    (∃ e : Class, IsSet e ∧ (∀ u : Class, u ∉ᴹ e) ∧ e ∈ᴹ x) ∧
    -- ∀ y ∈ x, s(y) = y ∪ {y} ∈ x:
    (∀ y : Class, y ∈ᴹ x →
      ∃ s : Class, IsSet s ∧ s ∈ᴹ x ∧
        ∀ u : Class, u ∈ᴹ s ↔ u ∈ᴹ y ∨ u = y)

/-! ─────────────────────────────────────────────────────────────────────────
    §1c · Par ordenado total + IsClassFun (requieren MK_Inf)
    ─────────────────────────────────────────────────────────────────────────
-/

-- Class es no-vacía: MK_Inf garantiza al menos un set.
noncomputable instance : Nonempty Class :=
  let ⟨x, _, _⟩ := MK_Inf; ⟨x⟩

-- Par ordenado total: igual a OPair cuando x, y son sets;
-- valor arbitrario (junk) en caso contrario.
noncomputable def opair (x y : Class) : Class :=
  if hx : IsSet x then
    if hy : IsSet y then OPair x y hx hy
    else Classical.choice inferInstance
  else Classical.choice inferInstance

-- Lema de reducción: bajo IsSet, opair coincide con OPair.
theorem opair_eq {x y : Class} (hx : IsSet x) (hy : IsSet y) :
    opair x y = OPair x y hx hy := by
  simp [opair, hx, hy]

local notation "⟪" x ", " y "⟫" => opair x y

-- El par ordenado de dos sets es un set.
theorem opair_isSet {x y : Class} (hx : IsSet x) (hy : IsSet y) :
    IsSet (⟪x, y⟫) := by
  rw [opair_eq hx hy]
  exact UPair_isSet (Sing_isSet hx) (UPair_isSet hx hy)

-- Inyectividad del par ordenado total (corolario de OPair_inj).
theorem opair_inj {x y x' y' : Class} (hx : IsSet x) (hy : IsSet y)
    (hx' : IsSet x') (hy' : IsSet y')
    (h : ⟪x, y⟫ = ⟪x', y'⟫) : x = x' ∧ y = y' := by
  rw [opair_eq hx hy, opair_eq hx' hy'] at h
  exact OPair_inj hx hy hx' hy' h

-- F es una clase-función (cada componente izquierda tiene exactamente una derecha).
def IsClassFun (F : Class) : Prop :=
  ∀ x y z : Class, IsSet x → IsSet y → IsSet z →
    ⟪x, y⟫ ∈ᴹ F → ⟪x, z⟫ ∈ᴹ F → y = z

-- ── A7. Class Comprehension Schema (MK-Comp) ──────────────────────────────
-- The hallmark of MK over NBG:
--   For *any* Lean Prop φ (including those quantifying over classes),
--   the collection {u : Set | φ u} exists as a class.
--
-- In NBG the schema is restricted to *predicative* formulas (no class
-- quantifiers); in MK the schema is *impredicative* (full second-order).
--
axiom MK_Comp :
  ∀ (φ : Class → Prop),
    ∃ Z : Class, ∀ u : Class, u ∈ᴹ Z ↔ IsSet u ∧ φ u

-- ── §1e · Comprensión de clase — classComp ────────────────────────────────

-- Abstracción total sobre MK_Comp: la clase de todos los sets que cumplen φ.
noncomputable def classComp (φ : Class → Prop) : Class :=
  Classical.choose (MK_Comp φ)

-- Caracterización de la membresía.
theorem classComp_mem (φ : Class → Prop) (u : Class) :
    u ∈ᴹ classComp φ ↔ IsSet u ∧ φ u :=
  Classical.choose_spec (MK_Comp φ) u

-- Notación libre: {| x | φ x |}  — todos los sets que satisfacen φ.
macro "{|" x:ident " | " p:term " |}" : term =>
  `(classComp (fun $x => $p))

-- Notación acotada: {| x ∈ᴹ X | φ x |}  — los sets de X que satisfacen φ.
macro "{|" x:ident " ∈ᴹ " X:term " | " p:term " |}" : term =>
  `(classComp (fun $x => $x ∈ᴹ $X ∧ $p))

-- ── §1d · Unión de clase ──────────────────────────────────────────────────

-- ⋃ᴹ X := {u | ∃ v, u ∈ᴹ v ∧ v ∈ᴹ X}
-- Existe siempre como clase; es set cuando X es set (MK_Union).
noncomputable def ClassUnion (X : Class) : Class :=
  {| u | ∃ v, u ∈ᴹ v ∧ v ∈ᴹ X |}

local prefix:110 "⋃ᴹ " => ClassUnion

-- Caracterización de la membresía en ⋃ᴹ X.
theorem classunion_mem (X u : Class) :
    u ∈ᴹ ⋃ᴹ X ↔ IsSet u ∧ ∃ v, u ∈ᴹ v ∧ v ∈ᴹ X :=
  classComp_mem _ u

-- Versión simplificada: cuando u ya es set, IsSet u es automático.
theorem classunion_mem' {X u : Class} (hu : IsSet u) :
    u ∈ᴹ ⋃ᴹ X ↔ ∃ v, u ∈ᴹ v ∧ v ∈ᴹ X := by
  rw [classunion_mem]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

-- La unión de un set es un set (consecuencia de MK_Union).
theorem classunion_isSet {X : Class} (hX : IsSet X) : IsSet (⋃ᴹ X) := by
  obtain ⟨z, hz_set, hz_mem⟩ := MK_Union X hX
  suffices h : ⋃ᴹ X = z by rw [h]; exact hz_set
  apply MK_Ext
  intro u hu
  rw [classunion_mem]
  constructor
  · rintro ⟨_, v, huv, hvX⟩
    exact (hz_mem u).mpr ⟨v, huv, hvX⟩
  · intro huz
    obtain ⟨v, huv, hvX⟩ := (hz_mem u).mp huz
    exact ⟨hu, v, huv, hvX⟩

-- ── A8. Substitution (Replacement) ───────────────────────────────────────
-- The image of a set under a class-function is a set.
-- (In MK this sometimes follows from Comp + other axioms,
--  but stating it explicitly keeps the axiom list transparent.)
axiom MK_Repl :
  ∀ (F x : Class), IsSet x → IsClassFun F →
    ∃ z : Class, IsSet z ∧
      ∀ v : Class, v ∈ᴹ z ↔ ∃ u : Class, u ∈ᴹ x ∧ ⟪u, v⟫ ∈ᴹ F

-- Si X es set, la comprensión acotada {| x ∈ᴹ X | φ x |} es set (vía MK_Repl).
-- Estrategia: la función identidad F := {⟪u,u⟫ | u ∈ X ∧ φ u} es clase-función;
-- su imagen sobre X coincide con {| x ∈ᴹ X | φ x |}, que por MK_Repl es set.
theorem bounded_comp_isSet {X : Class} (hX : IsSet X) (φ : Class → Prop) :
    IsSet {| x ∈ᴹ X | φ x |} := by
  -- Función identidad restringida a Z := {| x ∈ᴹ X | φ x |}
  let F : Class := {| p | ∃ u, IsSet u ∧ u ∈ᴹ X ∧ φ u ∧ p = ⟪u, u⟫ |}
  have hF_mem : ∀ p : Class,
      p ∈ᴹ F ↔ IsSet p ∧ ∃ u, IsSet u ∧ u ∈ᴹ X ∧ φ u ∧ p = ⟪u, u⟫ :=
    fun p => classComp_mem _ p
  -- F es clase-función
  have hF : IsClassFun F := by
    intro x y z hx hy hz h1 h2
    obtain ⟨_, u, hu, _, _, hxyu⟩ := (hF_mem _).mp h1
    obtain ⟨_, v, hv, _, _, hxzv⟩ := (hF_mem _).mp h2
    obtain ⟨hxu, hyu⟩ := opair_inj hx hy hu hu hxyu
    obtain ⟨hxv, hzv⟩ := opair_inj hx hz hv hv hxzv
    exact hyu.trans (hxu.symm.trans (hxv.trans hzv.symm))
  -- Por MK_Repl, la imagen de X bajo F es un set
  obtain ⟨z, hz_set, hz_mem⟩ := MK_Repl F X hX hF
  -- Mostramos que {| x ∈ᴹ X | φ x |} = z por MK_Ext
  suffices h : {| x ∈ᴹ X | φ x |} = z by rw [h]; exact hz_set
  apply MK_Ext
  intro u hu
  rw [classComp_mem, hz_mem]
  constructor
  · rintro ⟨_, huX, hφu⟩
    exact ⟨u, huX, (hF_mem _).mpr ⟨opair_isSet hu hu, u, hu, huX, hφu, rfl⟩⟩
  · rintro ⟨w, hwX, hwF⟩
    obtain ⟨_, v, hv, hvX, hφv, heq⟩ := (hF_mem _).mp hwF
    obtain ⟨_, huv⟩ := opair_inj ⟨X, hwX⟩ hu hv hv heq
    rw [huv]; exact ⟨hv, hvX, hφv⟩

-- ── §1f · Operaciones binarias de clase ──────────────────────────────────

-- ─ Unión binaria ──────────────────────────────────────────────────────────
noncomputable def BinUnion (A B : Class) : Class := {| x | x ∈ᴹ A ∨ x ∈ᴹ B |}

local infix:65 " ∪ᴹ " => BinUnion

theorem binunion_mem (A B u : Class) :
    u ∈ᴹ A ∪ᴹ B ↔ IsSet u ∧ (u ∈ᴹ A ∨ u ∈ᴹ B) :=
  classComp_mem _ u

theorem binunion_mem' {A B u : Class} (hu : IsSet u) :
    u ∈ᴹ A ∪ᴹ B ↔ u ∈ᴹ A ∨ u ∈ᴹ B := by
  rw [binunion_mem]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

-- A ∪ B es set cuando A y B son sets.
theorem binunion_isSet {A B : Class} (hA : IsSet A) (hB : IsSet B) :
    IsSet (A ∪ᴹ B) := by
  suffices h : A ∪ᴹ B = ⋃ᴹ (UPair A B hA hB) by
    rw [h]; exact classunion_isSet (UPair_isSet hA hB)
  apply MK_Ext
  intro u hu
  rw [binunion_mem' hu, classunion_mem' hu]
  constructor
  · rintro (huA | huB)
    · exact ⟨A, huA, (UPair_mem hA hB A).mpr (Or.inl rfl)⟩
    · exact ⟨B, huB, (UPair_mem hA hB B).mpr (Or.inr rfl)⟩
  · rintro ⟨v, huv, hvAB⟩
    rcases (UPair_mem hA hB v).mp hvAB with rfl | rfl
    · exact Or.inl huv
    · exact Or.inr huv

-- ─ Intersección binaria ───────────────────────────────────────────────────
noncomputable def BinInter (A B : Class) : Class := {| x | x ∈ᴹ A ∧ x ∈ᴹ B |}

local infix:70 " ∩ᴹ " => BinInter

theorem bininter_mem (A B u : Class) :
    u ∈ᴹ A ∩ᴹ B ↔ IsSet u ∧ u ∈ᴹ A ∧ u ∈ᴹ B :=
  classComp_mem _ u

theorem bininter_mem' {A B u : Class} (hu : IsSet u) :
    u ∈ᴹ A ∩ᴹ B ↔ u ∈ᴹ A ∧ u ∈ᴹ B := by
  rw [bininter_mem]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

-- A ∩ B es set cuando A es set (subclase de A, por bounded_comp_isSet).
theorem bininter_isSet_left {A B : Class} (hA : IsSet A) : IsSet (A ∩ᴹ B) :=
  bounded_comp_isSet hA (fun x => x ∈ᴹ B)

-- Simétrico: A ∩ B es set cuando B es set.
theorem bininter_isSet_right {A B : Class} (hB : IsSet B) : IsSet (A ∩ᴹ B) := by
  suffices h : A ∩ᴹ B = B ∩ᴹ A by
    rw [h]; exact bininter_isSet_left hB
  apply MK_Ext; intro u hu
  simp [bininter_mem' hu, And.comm]

-- ─ Diferencia de clases ───────────────────────────────────────────────────
noncomputable def ClassDiff (A B : Class) : Class := {| x | x ∈ᴹ A ∧ x ∉ᴹ B |}

local infix:70 " ∖ᴹ " => ClassDiff

theorem classdiff_mem (A B u : Class) :
    u ∈ᴹ A ∖ᴹ B ↔ IsSet u ∧ u ∈ᴹ A ∧ u ∉ᴹ B :=
  classComp_mem _ u

theorem classdiff_mem' {A B u : Class} (hu : IsSet u) :
    u ∈ᴹ A ∖ᴹ B ↔ u ∈ᴹ A ∧ u ∉ᴹ B := by
  rw [classdiff_mem]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

-- A \ B es set cuando A es set.
theorem classdiff_isSet {A B : Class} (hA : IsSet A) : IsSet (A ∖ᴹ B) :=
  bounded_comp_isSet hA (fun x => x ∉ᴹ B)

-- ─ Diferencia simétrica ───────────────────────────────────────────────────
noncomputable def SymDiff (A B : Class) : Class := (A ∖ᴹ B) ∪ᴹ (B ∖ᴹ A)

local infix:65 " △ᴹ " => SymDiff

-- A △ B es set cuando A y B son sets.
theorem symdiff_isSet {A B : Class} (hA : IsSet A) (hB : IsSet B) :
    IsSet (A △ᴹ B) :=
  binunion_isSet (classdiff_isSet hA) (classdiff_isSet hB)

-- ─ Complemento de clase ───────────────────────────────────────────────────
-- ∁ᴹ A := {x : Set | x ∉ A}
-- Es siempre una clase propia (salvo casos triviales).
-- En particular: ∁ᴹ ∅ = V (la clase universal), que no es set.
noncomputable def ClassCompl (A : Class) : Class := {| x | x ∉ᴹ A |}

local prefix:110 "∁ᴹ " => ClassCompl

theorem classcompl_mem (A u : Class) :
    u ∈ᴹ ∁ᴹ A ↔ IsSet u ∧ u ∉ᴹ A :=
  classComp_mem _ u

-- ── §1g · Conjuntos finitos por enumeración ──────────────────────────────

-- Singleton total: sing x = {x} si IsSet x; valor basura en caso contrario.
noncomputable def sing (x : Class) : Class :=
  if hx : IsSet x then Sing x hx else Classical.choice inferInstance

theorem sing_eq {x : Class} (hx : IsSet x) : sing x = Sing x hx :=
  dif_pos hx

theorem sing_isSet {x : Class} (hx : IsSet x) : IsSet (sing x) := by
  rw [sing_eq hx]; exact Sing_isSet hx

theorem sing_mem {x u : Class} (hx : IsSet x) : u ∈ᴹ sing x ↔ u = x := by
  rw [sing_eq hx]; exact Sing_mem hx u

-- Notación de enumeración finita: {| x₁, x₂, ..., xₙ |}
-- Separador ","  (distinto del separador "|" de la comprensión {| x | φ |}).
--   {| x |}              = sing x
--   {| x, y, ... |}      = sing x ∪ᴹ {| y, ... |}
syntax "{|" term,+ "|}" : term
macro_rules
  | `({| $x |})        => `(sing $x)
  | `({| $x, $xs,* |}) => `(sing $x ∪ᴹ {| $xs,* |})

-- isSet: {| x₁, ..., xₙ |} es set ⟺ cada xᵢ es set.
-- Construcción composicional:
--   n = 1 : sing_isSet hx
--   n ≥ 2 : binunion_isSet (sing_isSet hx₁) (binunion_isSet (sing_isSet hx₂) ...)
-- Caso base (azúcar para n = 1):
theorem finiteset_isSet₁ {x : Class} (hx : IsSet x) :
    IsSet {| x |} :=
  sing_isSet hx

-- ── §1h · Clases derivadas esenciales ────────────────────────────────────

-- ─ Clase vacía ────────────────────────────────────────────────────────────
noncomputable def Empty : Class := classComp (fun _ => False)

local notation "∅ᴹ" => Empty

theorem empty_mem (u : Class) : u ∉ᴹ ∅ᴹ :=
  fun h => ((classComp_mem _ u).mp h).2

-- ∅ᴹ es set: coincide con el vacío garantizado por MK_Inf.
theorem empty_isSet : IsSet ∅ᴹ := by
  obtain ⟨_, _, ⟨e, he_set, he_empty, _⟩, _⟩ := MK_Inf
  suffices h : ∅ᴹ = e by rw [h]; exact he_set
  apply MK_Ext; intro u _
  exact ⟨fun h => (empty_mem u h).elim, fun h => (he_empty u h).elim⟩

-- ─ Clase universal ────────────────────────────────────────────────────────
-- 𝐕ᴹ := {x : Set | True} — contiene exactamente todos los sets.
-- Es clase propia: si fuera set, se contendría a sí misma (contradice Foundation).
noncomputable def ClassV : Class := classComp (fun _ => True)

local notation "𝐕ᴹ" => ClassV

theorem classV_mem (u : Class) : u ∈ᴹ 𝐕ᴹ ↔ IsSet u :=
  ⟨fun h => ((classComp_mem _ u).mp h).1,
   fun h => (classComp_mem _ u).mpr ⟨h, trivial⟩⟩

-- ─ Clase potencia ─────────────────────────────────────────────────────────
noncomputable def PowerClass (X : Class) : Class := {| u | u ⊆ᴹ X |}

local prefix:110 "𝒫ᴹ " => PowerClass

theorem powclass_mem (X u : Class) :
    u ∈ᴹ 𝒫ᴹ X ↔ IsSet u ∧ u ⊆ᴹ X :=
  classComp_mem _ u

-- 𝒫ᴹ X es set cuando X es set (consecuencia de MK_Pow).
theorem powclass_isSet {X : Class} (hX : IsSet X) : IsSet (𝒫ᴹ X) := by
  obtain ⟨z, hz_set, hz_mem⟩ := MK_Pow X hX
  suffices h : 𝒫ᴹ X = z by rw [h]; exact hz_set
  apply MK_Ext; intro u _
  rw [powclass_mem, hz_mem]
  exact Iff.rfl

-- ─ Dominio de una clase ───────────────────────────────────────────────────
noncomputable def Dom (F : Class) : Class := {| x | ∃ y, ⟪x, y⟫ ∈ᴹ F |}

theorem dom_mem (F x : Class) :
    x ∈ᴹ Dom F ↔ IsSet x ∧ ∃ y, ⟪x, y⟫ ∈ᴹ F :=
  classComp_mem _ x

-- ─ Imagen de un conjunto bajo una clase ──────────────────────────────────
noncomputable def Img (F x : Class) : Class :=
  {| y | ∃ u, u ∈ᴹ x ∧ ⟪u, y⟫ ∈ᴹ F |}

theorem img_mem (F x v : Class) :
    v ∈ᴹ Img F x ↔ IsSet v ∧ ∃ u, u ∈ᴹ x ∧ ⟪u, v⟫ ∈ᴹ F :=
  classComp_mem _ v

-- Img F x es set cuando x es set e IsClassFun F (consecuencia de MK_Repl).
theorem img_isSet {F x : Class} (hx : IsSet x) (hF : IsClassFun F) :
    IsSet (Img F x) := by
  obtain ⟨z, hz_set, hz_mem⟩ := MK_Repl F x hx hF
  suffices h : Img F x = z by rw [h]; exact hz_set
  apply MK_Ext; intro v hv
  rw [img_mem, hz_mem]
  exact ⟨fun ⟨_, u, huX, huvF⟩ => ⟨u, huX, huvF⟩,
         fun ⟨u, huX, huvF⟩ => ⟨hv, u, huX, huvF⟩⟩

-- ── §1i · Álgebra booleana de clases ─────────────────────────────────────

-- ─ Helpers de membresía ───────────────────────────────────────────────────

-- ∅ᴹ tiene membresía equivalente a False.
theorem empty_mem_iff (u : Class) : u ∈ᴹ ∅ᴹ ↔ False :=
  ⟨empty_mem u, False.elim⟩

-- Complemento simplificado: IsSet u ya disponible.
theorem classcompl_mem' {A u : Class} (hu : IsSet u) :
    u ∈ᴹ ∁ᴹ A ↔ u ∉ᴹ A :=
  ⟨fun h => ((classcompl_mem A u).mp h).2,
   fun h => (classcompl_mem A u).mpr ⟨hu, h⟩⟩

-- IsSet X ↔ X ∈ᴹ 𝐕ᴹ.
theorem isSet_iff_mem_V {X : Class} : IsSet X ↔ X ∈ᴹ 𝐕ᴹ :=
  (classV_mem X).symm

-- ─ SubClass ───────────────────────────────────────────────────────────────

theorem subclass_refl (A : Class) : A ⊆ᴹ A :=
  fun _ h => h

theorem subclass_trans {A B C : Class} (h1 : A ⊆ᴹ B) (h2 : B ⊆ᴹ C) : A ⊆ᴹ C :=
  fun u h => h2 u (h1 u h)

theorem subclass_antisymm {A B : Class} (h1 : A ⊆ᴹ B) (h2 : B ⊆ᴹ A) : A = B :=
  MK_Ext A B fun u _ => ⟨h1 u, h2 u⟩

theorem empty_subclass (A : Class) : ∅ᴹ ⊆ᴹ A :=
  fun u h => (empty_mem u h).elim

theorem subclass_classV (A : Class) : A ⊆ᴹ 𝐕ᴹ :=
  fun u h => (classV_mem u).mpr (mem_isSet h)

theorem subclass_binunion_left (A B : Class) : A ⊆ᴹ A ∪ᴹ B :=
  fun _ h => (binunion_mem' (mem_isSet h)).mpr (Or.inl h)

theorem subclass_binunion_right (A B : Class) : B ⊆ᴹ A ∪ᴹ B :=
  fun _ h => (binunion_mem' (mem_isSet h)).mpr (Or.inr h)

theorem bininter_subclass_left (A B : Class) : A ∩ᴹ B ⊆ᴹ A :=
  fun _ h => ((bininter_mem' (mem_isSet h)).mp h).1

theorem bininter_subclass_right (A B : Class) : A ∩ᴹ B ⊆ᴹ B :=
  fun _ h => ((bininter_mem' (mem_isSet h)).mp h).2

-- ─ Unión binaria — álgebra ────────────────────────────────────────────────

theorem binunion_comm (A B : Class) : A ∪ᴹ B = B ∪ᴹ A := by
  apply MK_Ext; intro u hu
  simp only [binunion_mem' hu]; exact Or.comm

theorem binunion_assoc (A B C : Class) : (A ∪ᴹ B) ∪ᴹ C = A ∪ᴹ (B ∪ᴹ C) := by
  apply MK_Ext; intro u hu
  simp only [binunion_mem' hu]; exact or_assoc

theorem binunion_self (A : Class) : A ∪ᴹ A = A := by
  apply MK_Ext; intro u hu
  simp only [binunion_mem' hu]; exact or_self_iff

theorem binunion_empty_right (A : Class) : A ∪ᴹ ∅ᴹ = A := by
  apply MK_Ext; intro u hu
  simp [binunion_mem' hu, empty_mem_iff]

theorem binunion_empty_left (A : Class) : ∅ᴹ ∪ᴹ A = A := by
  rw [binunion_comm]; exact binunion_empty_right A

theorem binunion_classV_right (A : Class) : A ∪ᴹ 𝐕ᴹ = 𝐕ᴹ := by
  apply MK_Ext; intro u hu
  simp only [binunion_mem' hu, classV_mem]
  exact ⟨fun h => h.elim mem_isSet id, Or.inr⟩

theorem binunion_classV_left (A : Class) : 𝐕ᴹ ∪ᴹ A = 𝐕ᴹ := by
  rw [binunion_comm]; exact binunion_classV_right A

-- ─ Intersección binaria — álgebra ─────────────────────────────────────────

theorem bininter_comm (A B : Class) : A ∩ᴹ B = B ∩ᴹ A := by
  apply MK_Ext; intro u hu
  simp only [bininter_mem' hu]; exact And.comm

theorem bininter_assoc (A B C : Class) : (A ∩ᴹ B) ∩ᴹ C = A ∩ᴹ (B ∩ᴹ C) := by
  apply MK_Ext; intro u hu
  simp only [bininter_mem' hu]; exact and_assoc

theorem bininter_self (A : Class) : A ∩ᴹ A = A := by
  apply MK_Ext; intro u hu
  simp only [bininter_mem' hu]; exact and_self_iff

theorem bininter_empty_right (A : Class) : A ∩ᴹ ∅ᴹ = ∅ᴹ := by
  apply MK_Ext; intro u hu
  simp [bininter_mem' hu, empty_mem_iff]

theorem bininter_empty_left (A : Class) : ∅ᴹ ∩ᴹ A = ∅ᴹ := by
  rw [bininter_comm]; exact bininter_empty_right A

theorem bininter_classV_right (A : Class) : A ∩ᴹ 𝐕ᴹ = A := by
  apply MK_Ext; intro u hu
  simp only [bininter_mem' hu, classV_mem]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, mem_isSet h⟩⟩

theorem bininter_classV_left (A : Class) : 𝐕ᴹ ∩ᴹ A = A := by
  rw [bininter_comm]; exact bininter_classV_right A

-- ─ Distributividad ────────────────────────────────────────────────────────

theorem binunion_bininter_distrib (A B C : Class) :
    A ∪ᴹ (B ∩ᴹ C) = (A ∪ᴹ B) ∩ᴹ (A ∪ᴹ C) := by
  apply MK_Ext; intro u hu
  simp only [binunion_mem' hu, bininter_mem' hu]
  exact ⟨fun h => h.elim (fun ha => ⟨Or.inl ha, Or.inl ha⟩)
                          (fun ⟨hb, hc⟩ => ⟨Or.inr hb, Or.inr hc⟩),
         fun ⟨h1, h2⟩ => h1.elim Or.inl (fun hb => h2.elim Or.inl
                          (fun hc => Or.inr ⟨hb, hc⟩))⟩

theorem bininter_binunion_distrib (A B C : Class) :
    A ∩ᴹ (B ∪ᴹ C) = (A ∩ᴹ B) ∪ᴹ (A ∩ᴹ C) := by
  apply MK_Ext; intro u hu
  simp only [bininter_mem' hu, binunion_mem' hu]
  exact ⟨fun ⟨ha, h⟩ => h.elim (fun hb => Or.inl ⟨ha, hb⟩)
                                 (fun hc => Or.inr ⟨ha, hc⟩),
         fun h => h.elim (fun ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩)
                          (fun ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩)⟩

-- ─ Complemento ────────────────────────────────────────────────────────────

theorem compl_compl (A : Class) : ∁ᴹ (∁ᴹ A) = A := by
  apply MK_Ext; intro u hu
  rw [classcompl_mem' hu, classcompl_mem' hu]
  exact ⟨Classical.byContradiction, fun ha hna => hna ha⟩

theorem binunion_compl_self (A : Class) : A ∪ᴹ ∁ᴹ A = 𝐕ᴹ := by
  apply MK_Ext; intro u hu
  simp only [binunion_mem' hu, classcompl_mem' hu, classV_mem]
  exact ⟨fun _ => hu, fun _ => Classical.em (u ∈ᴹ A)⟩

theorem bininter_compl_self (A : Class) : A ∩ᴹ ∁ᴹ A = ∅ᴹ := by
  apply MK_Ext; intro u hu
  simp only [bininter_mem' hu, classcompl_mem' hu, empty_mem_iff]
  exact ⟨fun ⟨h, hn⟩ => hn h, False.elim⟩

-- ─ Leyes de De Morgan ─────────────────────────────────────────────────────

theorem compl_binunion (A B : Class) : ∁ᴹ (A ∪ᴹ B) = ∁ᴹ A ∩ᴹ ∁ᴹ B := by
  apply MK_Ext; intro u hu
  simp only [classcompl_mem' hu, binunion_mem' hu, bininter_mem' hu]
  exact ⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩,
         fun ⟨ha, hb⟩ h => h.elim ha hb⟩

theorem compl_bininter (A B : Class) : ∁ᴹ (A ∩ᴹ B) = ∁ᴹ A ∪ᴹ ∁ᴹ B := by
  apply MK_Ext; intro u hu
  simp only [classcompl_mem' hu, bininter_mem' hu, binunion_mem' hu]
  exact ⟨fun h => Classical.byContradiction (fun hn =>
           h ⟨Classical.byContradiction (fun ha => hn (Or.inl ha)),
              Classical.byContradiction (fun hb => hn (Or.inr hb))⟩),
         fun h ⟨ha, hb⟩ => h.elim (· ha) (· hb)⟩

-- ─ Diferencia = intersección con complemento ──────────────────────────────

theorem classdiff_eq_inter_compl (A B : Class) : A ∖ᴹ B = A ∩ᴹ ∁ᴹ B := by
  apply MK_Ext; intro u hu
  rw [classdiff_mem' hu, bininter_mem' hu, classcompl_mem' hu]

-- ── A9. Global Choice ─────────────────────────────────────────────────────
-- There exists a class C that selects an element from every non-empty set.
-- This is Kelley's (1955) original ninth axiom, included here as part of
-- the base MK system. It is stronger than AC (which only gives a set-function
-- for set-indexed families) because C is a proper class that works uniformly
-- over ALL sets simultaneously.
--
-- Three equivalent formulations (all provably equivalent over A1–A8):
--
--   (a) Class selector form:
-- axiom MK_GlobalChoice :
--   ∃ C : Class,
--     ∀ x : Class, IsSet x → (∃ u : Class, u ∈ᴹ x) →
--       ∃ u : Class, u ∈ᴹ x ∧ ⟪x, u⟫ ∈ᴹ C
--
--   (b) Class well-order form:
-- axiom MK_WO :
--   ∃ W : Class,
--     (∀ x y : Class, IsSet x → IsSet y → x ≠ y →
--       ⟪x, y⟫ ∈ᴹ W ∨ ⟪y, x⟫ ∈ᴹ W) ∧
--     (∀ x y : Class, ⟪x, y⟫ ∈ᴹ W → ¬ ⟪y, x⟫ ∈ᴹ W) ∧
--     (∀ X : Class, (∃ u : Class, IsSet u ∧ u ∈ᴹ X) →
--       ∃ m : Class, IsSet m ∧ m ∈ᴹ X ∧
--         ∀ u : Class, IsSet u → u ∈ᴹ X → ¬ ⟪u, m⟫ ∈ᴹ W)
--
--   (c) Zermelo form (every set can be well-ordered by some set-relation):
--       follows from (b) by restriction.
--
-- We adopt formulation (a) as the official axiom; (b) and (c) will be
-- derived theorems.
axiom MK_GlobalChoice :
  ∃ C : Class,
    ∀ x : Class, IsSet x → (∃ u : Class, u ∈ᴹ x) →
      ∃ u : Class, u ∈ᴹ x ∧ ⟪x, u⟫ ∈ᴹ C


/-! ─────────────────────────────────────────────────────────────────────────
    §3 · MK⁺ — Class Axiom Scheme of Choice (CAC)
    ─────────────────────────────────────────────────────────────────────────

  MK (with A1–A9 above) already has Global Choice as a single axiom.
  What MK⁺ adds is the *scheme* of class choice: for any *definable*
  class-relation R that is total on sets, a class-function selector exists.

  The difference:
    · A9 (Global Choice) gives one fixed class C that chooses from all sets.
    · CAC (MK⁺) gives, for each total class-relation R, a class-function
      F ⊆ R. This is strictly stronger because R can depend on parameters
      ranging over classes, yielding choices that A9 alone cannot provide.

  Reference: Felgner (1971) "Models of ZF-Set Theory", §IV;
             Lévy (1976) "The Role of Classes in Set Theory".
-/

-- ── MK⁺. Class Axiom Scheme of Choice (CAC) ──────────────────────────────
-- For any class-relation R that is total on sets (every set has an R-image),
-- there exists a class-function F ⊆ R with the same domain on sets.
--
-- In Lean a single `axiom` with universally quantified R captures the
-- whole scheme (one Lean Prop = one formula, so ∀ R already ranges over
-- all definable class-relations).
--
axiom MK_CAC :
  ∀ (R : Class),
    (∀ x : Class, IsSet x → ∃ y : Class, ⟪x, y⟫ ∈ᴹ R) →
    ∃ F : Class,
      (∀ x y z : Class, ⟪x, y⟫ ∈ᴹ F → ⟪x, z⟫ ∈ᴹ F → y = z) ∧  -- F is a function
      (∀ x : Class, IsSet x → ∃ y : Class, ⟪x, y⟫ ∈ᴹ F) ∧     -- F is total on sets
      (∀ x y : Class, ⟪x, y⟫ ∈ᴹ F → ⟪x, y⟫ ∈ᴹ R)              -- F ⊆ R


/-! ─────────────────────────────────────────────────────────────────────────
    §4 · ∃¹ en el contexto de clases
    ─────────────────────────────────────────────────────────────────────────

  Usamos ∃¹ (notación preferida de Prelim) en lugar de ∃!.
  Ambas expanden a ExistsUnique; ∃¹ evita colisiones con el ∃! de Lean.

  En el contexto MK, ∃¹ x, φ x significa:
    existe exactamente una *clase* X (o set, según contexto) que cumple φ.

  Usos típicos:
    · Unicidad de la clase vacía: ∃¹ E : Class, ∀ u, u ∉ᴹ E
    · Unicidad del segundo componente: ∃¹ y, ⟪x, y⟫ ∈ᴹ F
    · Relaciones funcionales: IsClassFun F → ∀ x, IsSet x → ∃¹ y, ⟪x, y⟫ ∈ᴹ F
-/

theorem unique_empty :
    ∃¹ E : Class, (∀ u : Class, u ∉ᴹ E) ∧ IsSet E := by
  -- Existencia: MK_Inf garantiza un set vacío e.
  obtain ⟨_, _, ⟨e, he_set, he_empty, _⟩, _⟩ := MK_Inf
  refine ExistsUnique.intro e ⟨he_empty, he_set⟩ ?_
  -- Unicidad: cualquier E' vacío coincide con e por MK_Ext.
  intro E' ⟨hE', _⟩
  apply MK_Ext
  intro u _
  exact ⟨fun h => absurd h (hE' u), fun h => absurd h (he_empty u)⟩

theorem classful_unique_image (F x : Class) (hF : IsClassFun F) (hx : IsSet x)
    (hu : ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F) : ∃¹ y : Class, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F := by
  obtain ⟨y, hy_set, hy⟩ := hu
  refine ExistsUnique.intro y ⟨hy_set, hy⟩ ?_
  intro z ⟨hz_set, hz⟩
  exact (hF x y z hx hy_set hz_set hy hz).symm


end MKplusCAC
