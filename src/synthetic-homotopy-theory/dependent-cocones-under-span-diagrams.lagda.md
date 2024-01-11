# Dependent cocones under span diagrams

```agda
module synthetic-homotopy-theory.dependent-cocones-under-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-homotopies
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
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮 := (A <-- S --> B)`
and a
[cocone structure](synthetic-homotopy-theory.cocones-under-span-diagrams.md) `c`
under `𝒮` with codomain `X`. Furthermore, consider a type family `P` over `X`.
In this case we may consider _dependent_ cocone structures on `P` over `c`.

A {{#concept "dependent cocone" Disambiguation="span diagram"}} `d` over
`(i , j , H)` on `P` consists of two dependent functions

```text
  i' : (a : A) → P (i a)
  j' : (b : B) → P (j b)
```

and a [dependent homotopy](foundation.dependent-homotopies.md)

```text
  i' ∘ f ~ j' ∘ g
```

over `H`.

## Definitions

### Dependent cocones

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X) (P : X → UU l5)
  where

  left-family-of-elements-dependent-cocone-span-diagram : UU (l1 ⊔ l5)
  left-family-of-elements-dependent-cocone-span-diagram =
    (a : domain-span-diagram s) → P (left-map-cocone-span-diagram s c a)

  right-family-of-elements-dependent-cocone-span-diagram : UU (l2 ⊔ l5)
  right-family-of-elements-dependent-cocone-span-diagram =
    (b : codomain-span-diagram s) → P (right-map-cocone-span-diagram s c b)

  dependent-homotopy-dependent-cocone-span-diagram :
    left-family-of-elements-dependent-cocone-span-diagram →
    right-family-of-elements-dependent-cocone-span-diagram → UU (l3 ⊔ l5)
  dependent-homotopy-dependent-cocone-span-diagram hA hB =
    dependent-homotopy
      ( λ _ → P)
      ( coherence-square-cocone-span-diagram s c)
      ( hA ∘ left-map-span-diagram s)
      ( hB ∘ right-map-span-diagram s)
  
  dependent-cocone-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  dependent-cocone-span-diagram =
    Σ ( left-family-of-elements-dependent-cocone-span-diagram)
      ( λ hA →
        Σ ( right-family-of-elements-dependent-cocone-span-diagram)
          ( dependent-homotopy-dependent-cocone-span-diagram hA))

  module _
    (d : dependent-cocone-span-diagram)
    where

    left-map-dependent-cocone-span-diagram :
      left-family-of-elements-dependent-cocone-span-diagram
    left-map-dependent-cocone-span-diagram = pr1 d

    right-map-dependent-cocone-span-diagram :
      right-family-of-elements-dependent-cocone-span-diagram
    right-map-dependent-cocone-span-diagram = pr1 (pr2 d)

    coherence-square-dependent-cocone-span-diagram :
      dependent-homotopy-dependent-cocone-span-diagram
        ( left-map-dependent-cocone-span-diagram)
        ( right-map-dependent-cocone-span-diagram)
    coherence-square-dependent-cocone-span-diagram = pr2 (pr2 d)
```

### Postcomposing dependent cocones with maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X) (P : X → UU l5)
  where

  dependent-cocone-map-span-diagram :
    ((x : X) → P x) → dependent-cocone-span-diagram s c P
  pr1 (dependent-cocone-map-span-diagram h) a =
    h (left-map-cocone-span-diagram s c a)
  pr1 (pr2 (dependent-cocone-map-span-diagram h)) b =
    h (right-map-cocone-span-diagram s c b)
  pr2 (pr2 (dependent-cocone-map-span-diagram h)) x =
    apd h (coherence-square-cocone-span-diagram s c x)
```

## Properties

### Characterization of identifications of dependent cocones

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X) (P : X → UU l5)
  (d : dependent-cocone-span-diagram s c P)
  where

  coherence-htpy-dependent-cocone-span-diagram :
    ( d' : dependent-cocone-span-diagram s c P)
    ( K :
      left-map-dependent-cocone-span-diagram s c P d ~
      left-map-dependent-cocone-span-diagram s c P d')
    ( L :
      right-map-dependent-cocone-span-diagram s c P d ~
      right-map-dependent-cocone-span-diagram s c P d') →
    UU (l3 ⊔ l5)
  coherence-htpy-dependent-cocone-span-diagram d' K L =
    ( x : spanning-type-span-diagram s) →
    ( ( coherence-square-dependent-cocone-span-diagram s c P d x) ∙
      ( L (right-map-span-diagram s x))) ＝
    ( ( ap
        ( tr P (coherence-square-cocone-span-diagram s c x))
        ( K (left-map-span-diagram s x))) ∙
      ( coherence-square-dependent-cocone-span-diagram s c P d' x))

  htpy-dependent-cocone-span-diagram :
    (d' : dependent-cocone-span-diagram s c P) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  htpy-dependent-cocone-span-diagram d' =
    Σ ( left-map-dependent-cocone-span-diagram s c P d ~
        left-map-dependent-cocone-span-diagram s c P d')
      ( λ K →
        Σ ( right-map-dependent-cocone-span-diagram s c P d ~
            right-map-dependent-cocone-span-diagram s c P d')
          ( coherence-htpy-dependent-cocone-span-diagram d' K))

  refl-htpy-dependent-cocone-span-diagram :
    htpy-dependent-cocone-span-diagram d
  pr1 refl-htpy-dependent-cocone-span-diagram = refl-htpy
  pr1 (pr2 refl-htpy-dependent-cocone-span-diagram) = refl-htpy
  pr2 (pr2 refl-htpy-dependent-cocone-span-diagram) = right-unit-htpy

  htpy-eq-dependent-cocone-span-diagram :
    (d' : dependent-cocone-span-diagram s c P) →
    d ＝ d' → htpy-dependent-cocone-span-diagram d'
  htpy-eq-dependent-cocone-span-diagram .d refl =
    refl-htpy-dependent-cocone-span-diagram

  module _
    (d' : dependent-cocone-span-diagram s c P)
    (p : d ＝ d')
    where

    left-htpy-eq-dependent-cocone-span-diagram :
      left-map-dependent-cocone-span-diagram s c P d ~
      left-map-dependent-cocone-span-diagram s c P d'
    left-htpy-eq-dependent-cocone-span-diagram =
      pr1 (htpy-eq-dependent-cocone-span-diagram d' p)

    right-htpy-eq-dependent-cocone-span-diagram :
      right-map-dependent-cocone-span-diagram s c P d ~
      right-map-dependent-cocone-span-diagram s c P d'
    right-htpy-eq-dependent-cocone-span-diagram =
      pr1 (pr2 (htpy-eq-dependent-cocone-span-diagram d' p))

    coherence-square-htpy-eq-dependent-cocone-span-diagram :
      coherence-htpy-dependent-cocone-span-diagram d'
        ( left-htpy-eq-dependent-cocone-span-diagram)
        ( right-htpy-eq-dependent-cocone-span-diagram)
    coherence-square-htpy-eq-dependent-cocone-span-diagram =
      pr2 (pr2 (htpy-eq-dependent-cocone-span-diagram d' p))

  abstract
    is-torsorial-htpy-dependent-cocone-span-diagram :
      is-torsorial htpy-dependent-cocone-span-diagram
    is-torsorial-htpy-dependent-cocone-span-diagram =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy
          ( left-map-dependent-cocone-span-diagram s c P d))
        ( left-map-dependent-cocone-span-diagram s c P d , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy
            ( right-map-dependent-cocone-span-diagram s c P d))
          ( right-map-dependent-cocone-span-diagram s c P d , refl-htpy)
          ( is-contr-equiv
            ( Σ ( dependent-homotopy
                  ( λ _ → P)
                  ( coherence-square-cocone-span-diagram s c)
                  ( left-map-dependent-cocone-span-diagram s c P d ∘
                    left-map-span-diagram s)
                  ( right-map-dependent-cocone-span-diagram s c P d ∘
                    right-map-span-diagram s))
                ( λ γ →
                  coherence-square-dependent-cocone-span-diagram s c P d ~ γ))
            ( equiv-tot (equiv-concat-htpy inv-htpy-right-unit-htpy))
            ( is-torsorial-htpy
              ( coherence-square-dependent-cocone-span-diagram s c P d))))

  abstract
    is-equiv-htpy-eq-dependent-cocone-span-diagram :
      (d' : dependent-cocone-span-diagram s c P) →
      is-equiv (htpy-eq-dependent-cocone-span-diagram d')
    is-equiv-htpy-eq-dependent-cocone-span-diagram =
      fundamental-theorem-id
        ( is-torsorial-htpy-dependent-cocone-span-diagram)
        ( htpy-eq-dependent-cocone-span-diagram)

    eq-htpy-dependent-cocone-span-diagram :
      (d' : dependent-cocone-span-diagram s c P) →
      htpy-dependent-cocone-span-diagram d' → d ＝ d'
    eq-htpy-dependent-cocone-span-diagram d' =
      map-inv-is-equiv (is-equiv-htpy-eq-dependent-cocone-span-diagram d')

    is-section-eq-htpy-dependent-cocone-span-diagram :
      (d' : dependent-cocone-span-diagram s c P) →
      is-section
        ( htpy-eq-dependent-cocone-span-diagram d')
        ( eq-htpy-dependent-cocone-span-diagram d')
    is-section-eq-htpy-dependent-cocone-span-diagram d' =
      is-section-map-inv-is-equiv
        ( is-equiv-htpy-eq-dependent-cocone-span-diagram d')

    is-retraction-eq-htpy-dependent-cocone-span-diagram :
      (d' : dependent-cocone-span-diagram s c P) →
      is-retraction
        ( htpy-eq-dependent-cocone-span-diagram d')
        ( eq-htpy-dependent-cocone-span-diagram d')
    is-retraction-eq-htpy-dependent-cocone-span-diagram d' =
      is-retraction-map-inv-is-equiv
        ( is-equiv-htpy-eq-dependent-cocone-span-diagram d')

  extensionality-dependent-cocone-span-diagram :
    (d' : dependent-cocone-span-diagram s c P) →
    (d ＝ d') ≃ htpy-dependent-cocone-span-diagram d'
  pr1 (extensionality-dependent-cocone-span-diagram d') =
    htpy-eq-dependent-cocone-span-diagram d'
  pr2 (extensionality-dependent-cocone-span-diagram d') =
    is-equiv-htpy-eq-dependent-cocone-span-diagram d'
```