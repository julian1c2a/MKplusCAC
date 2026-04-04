# Próximos Pasos: Desarrollo de MKplusCAC

Este documento detalla el plan estratégico y la hoja de ruta para la formalización matemática del proyecto **MKplusCAC** (Morse-Kelley + Class Axiom Scheme of Choice) en Lean 4.

## 1. Estado Actual de los Axiomas
Tras una revisión exhaustiva de `MKplusCACAxioms.lean`, podemos confirmar que **todos los axiomas fundacionales están correctamente definidos**. Esto incluye:
*   Extensionalidad, Fundación, Par, Unión, Partes e Infinitud (A1-A6).
*   El esquema de Comprensión de Clases (A7).
*   Reemplazo (A8).
*   El Axioma de Elección Global de Kelley (A9).
*   El Esquema Axiomático de Elección de Clases (CAC).

La base axiomática está completa y lista para soportar la teoría.

## 2. Metodología de Desarrollo por Capas
Para mantener el código organizado, libre de dependencias circulares y conceptualmente claro, implementaremos la teoría siguiendo una estricta jerarquía de capas en cada nuevo módulo:

1.  **Operaciones para Clases:** Definición pura de los constructos matemáticos a nivel general de clases (ej. uniones arbitrarias, producto cartesiano).
2.  **Teoremas para Clases (Operaciones):** Demostración de propiedades algebraicas y leyes lógicas que rigen estas operaciones.
3.  **Definición de Propiedades para Clases:** Definición de predicados sobre clases (ej. ser transitiva, ser una relación de equivalencia, ser una función).
4.  **Teoremas para Clases (Propiedades):** Resultados que derivan de las definiciones anteriores.
5.  **Operaciones Restringidas a Conjuntos:** Definiciones específicas (si son necesarias) para garantizar que las operaciones entre *sets* producen *sets*.
6.  **Definición de Propiedades Restringidas a Conjuntos:** Predicados exclusivos para conjuntos (ej. cardinalidad).
7.  **Teoremas para Conjuntos:** Teoremas que requieren la asunción de `IsSet X` para ser válidos o que son resultados clásicos de la teoría de conjuntos de Zermelo-Fraenkel.

## 3. Estrategia de Inclusión (Paralelismo con ZFC)
Un objetivo central de este proyecto es demostrar que la teoría clásica de conjuntos de Zermelo-Fraenkel con Elección (ZFC) está contenida dentro de MK. 
*   **Diseño:** Aunque nuestra ontología base distingue entre "Clases" y "Conjuntos" desde el minuto cero, los nombres de los teoremas de conjuntos, el orden de la materia y la estructura jerárquica emularán lo más fielmente posible a `ZfcSetTheory`.
*   **Beneficio:** Esto permitirá construir fácilmente un functor o mapeo lógico que demuestre formalmente la inclusión de ZFC en MK en etapas posteriores del proyecto.

## 4. Secuencia de Módulos (Hoja de Ruta Inmediata)
El desarrollo lógico comenzará construyendo las herramientas básicas de relaciones y funciones, para culminar en la teoría de ordinales. El orden estricto de los siguientes ficheros `.lean` será:

### Fase 1: `Relations.lean`
*   Pares ordenados (repaso y expansión).
*   Producto cartesiano de clases.
*   Definición de Relación binaria.
*   Dominio y Rango (Codominio).
*   Relación inversa.
*   Composición de relaciones.
*   Relaciones de equivalencia y orden.

### Fase 2: `Functions.lean`
*   Definición de función (como relación unívoca).
*   Dominio y valores de funciones (evaluación).
*   Inyectividad, sobreyectividad y biyectividad.
*   Composición de funciones e inversas.
*   Restricción de funciones.
*   Funciones sobre conjuntos y preservación de `IsSet` (Reemplazo).

### Fase 3: `Ordinals.lean`
*   Clases y conjuntos transitivos.
*   Relaciones bien fundadas y buen orden en MK.
*   Definición de Ordinales de von Neumann (conjuntos transitivos bien ordenados por $\in$).
*   Propiedades básicas de los ordinales.
*   Inducción y recursión transfinita (a nivel de clases y conjuntos).

---
*Este documento actuará como la guía principal para las próximas interacciones y el desarrollo de nuevo código en el proyecto.*