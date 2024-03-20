# Coforks

```agda
module synthetic-homotopy-theory.coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.codiagonal-maps-of-types
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.action-functions-cocones-under-span-diagrams
open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

A **cofork** of a parallel pair `f, g : A → B` with vertext `X` is a map
`e : B → X` together with a [homotopy](foundation.homotopies.md)
`H : e ∘ f ~ e ∘ g`. The name comes from the diagram

```text
     g
   ----->     e
 A -----> B -----> X
     f
```

which looks like a fork if you flip the arrows, hence a cofork.

Coforks are an analogue of
[cocones under spans](synthetic-homotopy-theory.cocones-under-span-diagrams.md)
for parallel pairs. The universal cofork of a pair is their
[coequalizer](synthetic-homotopy-theory.coequalizers.md).

## Definitions

### Coforks

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  cofork : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  cofork X = Σ (B → X) (λ e → e ∘ f ~ e ∘ g)

  module _
    { X : UU l3} (e : cofork X)
    where

    map-cofork : B → X
    map-cofork = pr1 e

    coherence-cofork : map-cofork ∘ f ~ map-cofork ∘ g
    coherence-cofork = pr2 e
```

### Homotopies of coforks

A homotopy between coforks with the same vertex is given by a homotopy between
the two maps, together with a coherence datum asserting that we may apply the
given homotopy and the appropriate cofork homotopy in either order.

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  where

  coherence-htpy-cofork :
    ( e e' : cofork f g X) →
    ( K : map-cofork f g e ~ map-cofork f g e') →
    UU (l1 ⊔ l3)
  coherence-htpy-cofork e e' K =
    ( (coherence-cofork f g e) ∙h (K ·r g)) ~
    ( (K ·r f) ∙h (coherence-cofork f g e'))

  htpy-cofork : cofork f g X → cofork f g X → UU (l1 ⊔ l2 ⊔ l3)
  htpy-cofork e e' =
    Σ ( map-cofork f g e ~ map-cofork f g e')
      ( coherence-htpy-cofork e e')
```

### Postcomposing coforks

Given a cofork `e : B → X` and a map `h : X → Y`, we may compose the two to get
a new cofork `h ∘ e`.

```text
     g
   ----->     e        h
 A -----> B -----> X -----> Y
     f
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} (e : cofork f g X)
  where

  cofork-map : {l : Level} {Y : UU l} → (X → Y) → cofork f g Y
  pr1 (cofork-map h) = h ∘ map-cofork f g e
  pr2 (cofork-map h) = h ·l (coherence-cofork f g e)
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  where

  reflexive-htpy-cofork : (e : cofork f g X) → htpy-cofork f g e e
  pr1 (reflexive-htpy-cofork e) = refl-htpy
  pr2 (reflexive-htpy-cofork e) = right-unit-htpy

  htpy-cofork-eq :
    ( e e' : cofork f g X) → (e ＝ e') → htpy-cofork f g e e'
  htpy-cofork-eq e .e refl = reflexive-htpy-cofork e

  abstract
    is-torsorial-htpy-cofork :
      ( e : cofork f g X) → is-torsorial (htpy-cofork f g e)
    is-torsorial-htpy-cofork e =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-cofork f g e))
        ( map-cofork f g e , refl-htpy)
        ( is-contr-is-equiv'
          ( Σ ( map-cofork f g e ∘ f ~ map-cofork f g e ∘ g)
              ( λ K → coherence-cofork f g e ~ K))
          ( tot (λ K M → right-unit-htpy ∙h M))
          ( is-equiv-tot-is-fiberwise-equiv
            ( is-equiv-concat-htpy right-unit-htpy))
          ( is-torsorial-htpy (coherence-cofork f g e)))

    is-equiv-htpy-cofork-eq :
      ( e e' : cofork f g X) → is-equiv (htpy-cofork-eq e e')
    is-equiv-htpy-cofork-eq e =
      fundamental-theorem-id (is-torsorial-htpy-cofork e) (htpy-cofork-eq e)

  eq-htpy-cofork :
    ( e e' : cofork f g X) → htpy-cofork f g e e' → e ＝ e'
  eq-htpy-cofork e e' = map-inv-is-equiv (is-equiv-htpy-cofork-eq e e')
```

### Postcomposing a cofork by identity is the identity

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X)
  where

  cofork-map-id : cofork-map f g e id ＝ e
  cofork-map-id =
    eq-htpy-cofork f g
      ( cofork-map f g e id)
      ( e)
      ( refl-htpy , (right-unit-htpy ∙h (ap-id ∘ coherence-cofork f g e)))
```

### Postcomposing coforks distributes over function composition

```text
     g
   ----->     e        h        k
 A -----> B -----> X -----> Y -----> Z
     f
```

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} {Y : UU l4} {Z : UU l5}
  ( e : cofork f g X)
  where

  cofork-map-comp :
    (h : X → Y) (k : Y → Z) →
    cofork-map f g e (k ∘ h) ＝ cofork-map f g (cofork-map f g e h) k
  cofork-map-comp h k =
    eq-htpy-cofork f g
      ( cofork-map f g e (k ∘ h))
      ( cofork-map f g (cofork-map f g e h) k)
      ( refl-htpy , (right-unit-htpy ∙h (ap-comp k h ∘ coherence-cofork f g e)))
```

### Coforks are special cases of cocones under spans

The type of coforks of parallel pairs is equivalent to the type of
[cocones](synthetic-homotopy-theory.cocones-under-span-diagrams.md) under the
span

```text
     ∇         [f,g]
A <----- A + A -----> B.
```

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  left-map-span-cocone-cofork : A + A → A
  left-map-span-cocone-cofork = codiagonal A

  right-map-span-cocone-cofork : A + A → B
  right-map-span-cocone-cofork (inl a) = f a
  right-map-span-cocone-cofork (inr a) = g a

  span-diagram-cofork : span-diagram l1 l2 l1
  span-diagram-cofork =
    make-span-diagram
      ( left-map-span-cocone-cofork)
      ( right-map-span-cocone-cofork)

  module _
    { l3 : Level} {X : UU l3}
    where

    cofork-cocone-span-diagram-cofork :
      cocone-span-diagram span-diagram-cofork X →
      cofork f g X
    pr1 (cofork-cocone-span-diagram-cofork c) =
      right-map-cocone-span-diagram span-diagram-cofork c
    pr2 (cofork-cocone-span-diagram-cofork c) =
      ( ( inv-htpy
          ( coherence-square-cocone-span-diagram span-diagram-cofork c)) ·r
        ( inl)) ∙h
      ( ( coherence-square-cocone-span-diagram span-diagram-cofork c) ·r
        ( inr))

    left-map-cocone-span-diagram-cofork-cofork : cofork f g X → A → X
    left-map-cocone-span-diagram-cofork-cofork e = map-cofork f g e ∘ f

    right-map-cocone-span-diagram-cofork-cofork : cofork f g X → B → X
    right-map-cocone-span-diagram-cofork-cofork e = map-cofork f g e

    coherence-square-cocone-span-diagram-cofork-cofork :
      ( e : cofork f g X) →
      coherence-square-maps
        ( right-map-span-cocone-cofork)
        ( left-map-span-cocone-cofork)
        ( right-map-cocone-span-diagram-cofork-cofork e)
        ( left-map-cocone-span-diagram-cofork-cofork e)
    coherence-square-cocone-span-diagram-cofork-cofork e (inl a) =
      refl
    coherence-square-cocone-span-diagram-cofork-cofork e (inr a) =
      coherence-cofork f g e a

    cocone-span-diagram-cofork-cofork :
      cofork f g X →
      cocone-span-diagram span-diagram-cofork X
    pr1 (cocone-span-diagram-cofork-cofork e) =
      left-map-cocone-span-diagram-cofork-cofork e
    pr1 (pr2 (cocone-span-diagram-cofork-cofork e)) =
      right-map-cocone-span-diagram-cofork-cofork e
    pr2 (pr2 (cocone-span-diagram-cofork-cofork e)) =
      coherence-square-cocone-span-diagram-cofork-cofork e

    abstract
      is-section-cocone-span-diagram-cofork-cofork :
        is-section
          ( cofork-cocone-span-diagram-cofork)
          ( cocone-span-diagram-cofork-cofork)
      is-section-cocone-span-diagram-cofork-cofork e =
        eq-htpy-cofork f g
          ( cofork-cocone-span-diagram-cofork
            ( cocone-span-diagram-cofork-cofork e))
          ( e)
          ( refl-htpy , right-unit-htpy)

      is-retraction-cocone-span-diagram-cofork-cofork :
        is-retraction
          ( cofork-cocone-span-diagram-cofork)
          ( cocone-span-diagram-cofork-cofork)
      is-retraction-cocone-span-diagram-cofork-cofork c =
        eq-htpy-cocone-span-diagram
          ( span-diagram-cofork)
          ( cocone-span-diagram-cofork-cofork
            ( cofork-cocone-span-diagram-cofork c))
          ( c)
          ( ( ( inv-htpy
                ( coherence-square-cocone-span-diagram span-diagram-cofork
                  ( c))) ·r
              ( inl)) ,
            ( refl-htpy) ,
            ( ind-coproduct _
              ( inv-htpy
                ( left-inv-htpy
                  ( ( coherence-square-cocone-span-diagram
                      ( span-diagram-cofork)
                      ( c)) ·r
                    ( inl))))
              ( right-unit-htpy)))

    is-equiv-cofork-cocone-span-diagram-cofork :
      is-equiv cofork-cocone-span-diagram-cofork
    is-equiv-cofork-cocone-span-diagram-cofork =
      is-equiv-is-invertible
        ( cocone-span-diagram-cofork-cofork)
        ( is-section-cocone-span-diagram-cofork-cofork)
        ( is-retraction-cocone-span-diagram-cofork-cofork)

    equiv-cofork-cocone-span-diagram-cofork :
      cocone-span-diagram span-diagram-cofork X ≃
      cofork f g X
    pr1 equiv-cofork-cocone-span-diagram-cofork =
      cofork-cocone-span-diagram-cofork
    pr2 equiv-cofork-cocone-span-diagram-cofork =
      is-equiv-cofork-cocone-span-diagram-cofork

  triangle-cofork-cocone :
    { l3 l4 : Level} {X : UU l3} {Y : UU l4} →
    ( e : cofork f g X) →
    coherence-triangle-maps
      ( cofork-map f g e {Y = Y})
      ( cofork-cocone-span-diagram-cofork)
      ( cocone-map-span-diagram
        ( span-diagram-cofork)
        ( cocone-span-diagram-cofork-cofork e))
  triangle-cofork-cocone e h =
    eq-htpy-cofork f g
      ( cofork-map f g e h)
      ( cofork-cocone-span-diagram-cofork
        ( cocone-map-span-diagram
          ( span-diagram-cofork)
          ( cocone-span-diagram-cofork-cofork e)
          ( h)))
      ( refl-htpy ,
        right-unit-htpy)
```
