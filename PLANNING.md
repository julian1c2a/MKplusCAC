# Development Plan — MKplusCAC

**Last updated:** 2026-04-16 00:00 **Author**: Julián Calderón Almendros

> Este documento es el plan maestro de desarrollo. Complementa NEXT-STEPS.md (que es operativo y de corto plazo) con una visión arquitectural completa. La prioridad inmediata es conseguir la misma comodidad operacional que existe en ZfcSetTheory antes de avanzar hacia resultados más profundos.


## 0. Estado de partida (2026-04-16)

| Módulo | Estado | Sorrys |
| - | - | - |
| `Prelim.lean` | 🧊 Frozen | 0 |
| `MKplusCACAxioms.lean` | ✅ Complete (Locked) | 0 |
| `Relations.lean` | ✅ Complete (Locked) | 0 |
| `Functions.lean` | 🔄 In progress | 2 |


**Deuda técnica inmediata**: `Functions.lean` tiene dos `sorry` pendientes en `surjective\_iff\_forall\_exists\_app`. Son el primer obstáculo antes de avanzar.


## 1. Objetivo Estratégico

El objetivo no es sólo formalizar MK+CAC, sino hacerlo con la misma **comodidad operacional** que ZfcSetTheory: un conjunto de herramientas (lemas de caracterización, lemas auxiliares de set-hood, notaciones y tácticas reutilizables) que permita probar resultados matemáticos sin fricción constante con la infraestructura.

En MK el desafío adicional frente a ZFC es que la distinción **clase / conjunto** aparece en cada enunciado. La infraestructura debe absorber esa fricción lo más posible.


## 2. Principios Arquitecturales

### P1 — Lema `\_iff` + lema `\_iff'` para cada operación

Cada operación `op` debe tener:

- `mem\_op\_iff` : versión con `IsSet u` como parte de la conclusión (sin hipótesis de set-hood)

- `mem\_op\_iff'` : versión simplificada con `(hu : IsSet u)` como hipótesis implícita

El par es lo que permite usar `simp` o `rw` sin tener que gestionar manualmente el testigo de set-hood en cada paso.

### P2 — Lema `isSet\_op` para cada operación que produce sets

Cada operación definida sobre sets debe tener su lema `isSet\_op` que certifica que el resultado es un set. Esto evita el patrón repetitivo de tener que abrir la definición para extraer el testigo.

### P3 — Lemas `mem\_dom\_iff'` y `mem\_rng\_iff'`

Las versiones primadas (con `IsSet` como hipótesis) son las más usadas en práctica. Deben existir en `MKplusCACAxioms.lean` y `Relations.lean`.

### P4 — `app` completamente especificado

La función de evaluación `F⦑x⦒` debe tener lemas que cubran:

- `app\_mem\_rng` : `x ∈ dom F → F⦑x⦒ ∈ rng F`

- `app\_unique` : `IsFun F → IsSet x → ⟪x, y⟫ ∈ F → F⦑x⦒ = y`

- `opair\_app\_mem` : `x ∈ dom F → ⟪x, F⦑x⦒⟫ ∈ F`

### P5 — Infraestructura de buen orden antes de ordinales

Los ordinales en MK se definen como conjuntos transitivos bien ordenados por ∈. La infraestructura de buen orden (relaciones bien fundadas, mínimo de subclases no vacías) debe estar sólida antes de abrir `Ordinals.lean`.


## 3. Fases de Desarrollo


### FASE 0 — Cerrar la deuda técnica en Functions.lean

**Prioridad: INMEDIATA** **Estimación: 1–2 sesiones**

Resolver los dos `sorry` en `surjective\_iff\_forall\_exists\_app`:

1. **sorry 1**: `y ∈ rng F` → `y ∈ B` en la dirección `←` del iff. Requiere un lema `mem\_rng\_of\_app` o similar.

2. **sorry 2**: `⟪x, y⟫ ∈ F` desde la hipótesis de aplicación definida. Requiere `opair\_app\_mem` con las hipótesis correctas.

**Entregable**: `Functions.lean` sin `sorry`, listo para freezar.


### FASE 1 — Completar y consolidar Functions.lean

**Prioridad: ALTA** **Estimación: 2–3 sesiones**

Añadir los lemas de infraestructura que faltan:

#### 1.1 Lemas sobre `app`

- `app\_unique` : `IsFun F → IsSet x → ⟪x, y⟫ ∈ F → F⦑x⦒ = y`

- `opair\_app\_mem` : `IsFun F → x ∈ dom F → ⟪x, F⦑x⦒⟫ ∈ F`

- `app\_mem\_rng` : `IsFun F → x ∈ dom F → F⦑x⦒ ∈ rng F`

- `isSet\_app'` : versión de `isSet\_app` con hipótesis `x ∈ dom F`

#### 1.2 Lemas sobre dominio y rango

- `mem\_dom\_iff'` : versión con `(hx : IsSet x)` como hipótesis

- `rng\_subset\_of\_fun` : `IsFunFromTo F A B → rng F ⊆ B`

- `dom\_restrict\_eq` : `dom (F ↾ A) = dom F ∩ A`

#### 1.3 Lemas sobre inyectividad / sobreyectividad

- `bijective\_iff` : caracterización explícita de `IsBijective`

- `inverse\_is\_fun` : `IsInjective F → IsFun F⁻¹`

- `comp\_is\_fun` : `IsFun F → IsFun G → IsFun (F ∘ G)`

- `injective\_comp` : inyectividad se preserva por composición

- `surjective\_comp` : sobreyectividad se preserva por composición

#### 1.4 Lemas de isSet para operaciones

- `isSet\_rng\_of\_isSet\_dom` : si `dom F` es set e `IsFun F`, entonces `rng F` es set (vía MK\_Repl)

- `isSet\_restrict` : `F ↾ A` es set si `F` y `A` son sets

**Entregable**: `Functions.lean` frozen, lista de exports completa en REFERENCE.md.


### FASE 2 — WellFounded.lean

**Prioridad: ALTA (bloquea Ordinals)** **Estimación: 3–4 sesiones**

Infraestructura de relaciones bien fundadas y buen orden sobre clases.

#### 2.1 Definiciones

```
IsWellFounded (R : Class) : Prop  
  := IsRel R ∧ ∀ X, (∃ u, IsSet u ∧ u ∈ X) →  
       ∃ m, IsSet m ∧ m ∈ X ∧ ∀ u, IsSet u → u ∈ X → ⟪u, m⟫ ∉ R  
  
IsWellOrder (R A : Class) : Prop  
  := StrictTotalOrderOn R A ∧ IsWellFounded R  
  
IsTransitiveClass (X : Class) : Prop  
  := ∀ u v, IsSet u → IsSet v → u ∈ v → v ∈ X → u ∈ X
```

#### 2.2 Teoremas clave

- `wf\_has\_minimal` : todo subconjunto no vacío tiene mínimo (es la definición)

- `wf\_irrefl` : bien fundada ⟹ irreflexiva (Foundation)

- `wf\_asymm` : bien fundada ⟹ asimétrica

- `mem\_wf` : la relación ∈ₘ restringida a cualquier conjunto es bien fundada (via MK\_Found)

- `wf\_induction` : esquema de inducción bien fundada (sobre sets)

#### 2.3 Principio de inducción sobre ∈

Esto es el corazón que desbloquea la recursión transfinita:

```
theorem mem\_induction (φ : Class → Prop)  
    (h : ∀ x, IsSet x → (∀ u, IsSet u → u ∈ x → φ u) → φ x) :  
    ∀ x, IsSet x → φ x
```

Derivado de MK\_Found (Foundation implica inducción ∈).

**Entregable**: `WellFounded.lean` completo y frozen.


### FASE 3 — Ordinals.lean

**Prioridad: ALTA** **Estimación: 4–6 sesiones**

El módulo central de la teoría.

#### 3.1 Definiciones

```
IsOrd (α : Class) : Prop  
  := IsSet α ∧ IsTransitiveClass α ∧ IsWellOrder Mem α  
  
-- Sucesor de von Neumann: s(α) = α ∪ \{α\}  
succ (α : Class) : Class  
  
-- Ordinal cero  
ordZero : Class  -- = ∅  
  
-- Ordinal límite  
IsLimitOrd (α : Class) : Prop  
  := IsOrd α ∧ α ≠ ordZero ∧ ∀ β, IsOrd β → β ∈ α → succ β ∈ α
```

#### 3.2 Teoremas básicos

- `isOrd\_empty` : ∅ es ordinal

- `isOrd\_succ` : si α es ordinal, succ(α) es ordinal

- `mem\_ord\_is\_ord` : todo miembro de un ordinal es ordinal (herencia)

- `ord\_trichotomy` : ∀ α β ordinales, α ∈ β ∨ α = β ∨ β ∈ α

- `ord\_linear` : los ordinales están linealmente ordenados por ∈

- `ord\_wf` : ∈ es bien fundada en la clase de todos los ordinales

#### 3.3 Inducción y recursión transfinita

```
theorem ord\_induction (φ : Class → Prop)  
    (h : ∀ α, IsOrd α → (∀ β, IsOrd β → β ∈ α → φ β) → φ α) :  
    ∀ α, IsOrd α → φ α  
  
-- La recursión transfinita requiere CAC para definir funciones de clase  
theorem ord\_recursion (G : Class) (hG : IsClassFun G) :  
    ∃ F, IsFun F ∧ dom F = Ord ∧  
      ∀ α, IsOrd α → F⦑α⦒ = G⦑F ↾ α⦒
```

**Entregable**: `Ordinals.lean` completo y frozen.


### FASE 4 — NatNumbers.lean

**Prioridad: MEDIA** **Estimación: 3–4 sesiones**

Los números naturales como ordinales finitos de von Neumann.

#### 4.1 Definiciones

```
IsFinOrd (n : Class) : Prop  
  := IsOrd n ∧ IsOrd (succ n) ∧ ¬ IsLimitOrd n  -- equivalente a "finito"  
  
-- ω como el mínimo ordinal límite (su existencia viene de MK\_Inf)  
omega : Class  
  
IsNat (n : Class) : Prop := n ∈ ω
```

#### 4.2 Relación con MK\_Inf

MK\_Inf garantiza un conjunto inductivo; `omega` se define como la intersección de todos los conjuntos inductivos (que existe por MK\_Comp). Los naturales son exactamente los miembros de `omega`.

#### 4.3 Teoremas

- `isOrd\_omega` : ω es ordinal (y es límite)

- `nat\_zero` : 0 := ∅ ∈ ω

- `nat\_succ` : n ∈ ω → succ(n) ∈ ω

- `nat\_induction` : esquema de inducción sobre ω

- `omega\_least\_limit` : ω es el mínimo ordinal límite

**Entregable**: `NatNumbers.lean` completo y frozen.


### FASE 5 — Cardinals.lean

**Prioridad: MEDIA** **Estimación: 4–5 sesiones**

Cardinalidad via biyecciones, sin necesidad de números de Scott. En MK con Global Choice, cada conjunto tiene un número cardinal definido como el menor ordinal equipotente.

#### 5.1 Definiciones

```
Equipotent (A B : Class) : Prop  
  := ∃ F, IsBijective F A B  
  
card (x : Class) : Class   -- el cardinal de x (menor ordinal equipotente)  
  
IsCard (κ : Class) : Prop  -- κ es un número cardinal  
  := IsOrd κ ∧ ∀ β, IsOrd β → β ∈ κ → ¬ Equipotent β κ
```

#### 5.2 Teoremas

- `equipotent\_refl`, `equipotent\_symm`, `equipotent\_trans`

- `cantor\_no\_surjection` : ¬ Equipotent x (𝒫 x)

- `cantor\_schroeder\_bernstein`

- `card\_of\_nat` : el cardinal de n ∈ ω es n mismo

- `aleph\_zero` : ω es el primer cardinal infinito (ℵ₀)

**Entregable**: `Cardinals.lean` completo y frozen.


### FASE 6 — ZfcEmbedding.lean

**Prioridad: BAJA (largo plazo)** **Estimación: 6–8 sesiones**

El objetivo estratégico declarado: mostrar que ZFC está contenida en MK+CAC.

#### 6.1 Estrategia

Definir la subcategoría de "sets" en MK y verificar que satisface cada axioma de ZFC con los conjuntos (no clases) como universo de discurso.

#### 6.2 Teoremas

- `zfc\_extensionality` : MK\_Ext restringido a sets implica ZFC-Ext

- `zfc\_separation` : `isSet\_sep` implica ZFC-Sep

- `zfc\_replacement` : MK\_Repl implica ZFC-Repl

- `zfc\_powerset` : MK\_Pow implica ZFC-Pow

- `zfc\_union` : MK\_Union implica ZFC-Union

- `zfc\_infinity` : MK\_Inf implica ZFC-Inf

- `zfc\_choice` : MK\_GlobalChoice implica ZFC-AC


## 4. Módulos de Infraestructura Transversal

Estos módulos pueden crearse en paralelo a las fases anteriores:

### 4.1 FiniteSets.lean (entre Fases 1 y 3)

Conjuntos finitos enumerados y sus propiedades básicas. Extiende la notación `\{| x₁, ..., xₙ |\}` ya definida en `MKplusCACAxioms.lean`.

```
isSet\_finset₂  : IsSet x → IsSet y → IsSet \{| x, y |\}  
isSet\_finset₃  : IsSet x → IsSet y → IsSet z → IsSet \{| x, y, z |\}  
mem\_finset\_iff : u ∈ \{| x₁, ..., xₙ |\} ↔ u = x₁ ∨ ... ∨ u = xₙ
```

### 4.2 ClassAlgebra.lean (extensión de MKplusCACAxioms)

Lemas algebraicos adicionales que se descubran necesarios durante el desarrollo (distributividad extendida, leyes de absorción, etc.). Creado como extensión para evitar descongelar `MKplusCACAxioms.lean`.

### 4.3 SetArithmetic.lean (después de NatNumbers)

Operaciones aritméticas sobre ordinales: suma, producto, exponenciación. Definidas por recursión transfinita.


## 5. Dependencias entre Fases

```
Prelim  
  └── MKplusCACAxioms  
        ├── Relations  
        │     └── Functions \[FASE 0+1\]  
        │           ├── WellFounded \[FASE 2\]  
        │           │     └── Ordinals \[FASE 3\]  
        │           │           ├── NatNumbers \[FASE 4\]  
        │           │           └── Cardinals \[FASE 5\]  
        │           │                 └── ZfcEmbedding \[FASE 6\]  
        │           └── FiniteSets \[transversal\]  
        └── ClassAlgebra \[transversal, extensión\]
```


## 6. Convenciones de Desarrollo a Mantener

### 6.1 Cada módulo nuevo sigue este patrón interno

```
Section 1: Operaciones (definiciones)  
Section 2: Lemas de caracterización (\_iff, \_iff')  
Section 3: Lemas de isSet para cada operación  
Section 4: Propiedades algebraicas  
Section 5: Resultados avanzados  
Section 6: Exports
```

### 6.2 Protocolo de `sorry`

- Ningún módulo se congela con `sorry`.

- Si un `sorry` bloquea el avance, se anota en NEXT-STEPS.md y se crea un módulo "stub" que no se importa todavía.

### 6.3 Notaciones locales

Todas las notaciones permanecen `local` dentro de cada módulo. Las notaciones globales se declaran **sólo** en `MKplusCACAxioms.lean` si son parte del lenguaje primitivo del proyecto.

### 6.4 Actualización de REFERENCE.md

Obligatoria al final de cada sesión que modifique un `.lean`. Incluir: nuevas definiciones, nuevos teoremas, cambios de status.


## 7. Criterio de Éxito por Fase

| Fase | Criterio de éxito |
| - | - |
| 0 | `check-sorry.bash` devuelve 0 |
| 1 | `Functions.lean` frozen, exports completos |
| 2 | `mem\_induction` probado sin sorry |
| 3 | `ord\_trichotomy` y `ord\_induction` probados |
| 4 | `nat\_induction` probado, ω caracterizado |
| 5 | `cantor\_no\_surjection` probado |
| 6 | Todos los axiomas ZFC verificados sobre la subcategoría de sets |



## 8. Notas sobre MK vs ZFC en la Práctica

El trabajo en MK tiene una fricción específica respecto a ZFC:

1. **Cada lema necesita `IsSet` en las hipótesis** donde ZFC lo asumiría implícitamente. Mitigaremos esto con lemas `\_iff'` que toman `IsSet` como hipótesis implícita.

2. **Las definiciones son sobre `Class`** pero los resultados interesantes son sobre sets. El patrón será: definir en general, restringir a sets para los teoremas de existencia.

3. **CAC vs. Choice en ZFC**: en MK+CAC podemos elegir sobre relaciones de clase, lo que nos da más poder. Los teoremas que en ZFC requieren AC aquí serán más fuertes (válidos para clases, no sólo para sets).


*Documento vivo. Actualizar al inicio de cada fase con el estado real.*

**Author**: Julián Calderón Almendros *Last updated: 2026-04-16 00:00*

