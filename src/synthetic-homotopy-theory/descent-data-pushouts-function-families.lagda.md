# Descent data for families of functions over pushouts

```agda
{-# OPTIONS --lossy-unification #-}
module synthetic-homotopy-theory.descent-data-pushouts-function-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.postcomposition-functions
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.morphisms-descent-data-pushouts
open import synthetic-homotopy-theory.sections-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5)
  (Q : family-with-descent-data-pushout c l6)
  where

  family-cocone-family-with-descent-data-pushout-function-family :
    X → UU (l5 ⊔ l6)
  family-cocone-family-with-descent-data-pushout-function-family x =
    family-cocone-family-with-descent-data-pushout P x →
    family-cocone-family-with-descent-data-pushout Q x

  descent-data-pushout-function-family :
    descent-data-pushout 𝒮 (l5 ⊔ l6)
  pr1 descent-data-pushout-function-family a =
    left-family-family-with-descent-data-pushout P a →
    left-family-family-with-descent-data-pushout Q a
  pr1 (pr2 descent-data-pushout-function-family) b =
    right-family-family-with-descent-data-pushout P b →
    right-family-family-with-descent-data-pushout Q b
  pr2 (pr2 descent-data-pushout-function-family) s =
    ( equiv-postcomp
      ( right-family-family-with-descent-data-pushout P
        ( right-map-span-diagram 𝒮 s))
      ( equiv-family-family-with-descent-data-pushout Q s)) ∘e
    ( equiv-precomp
      ( inv-equiv (equiv-family-family-with-descent-data-pushout P s))
      ( left-family-family-with-descent-data-pushout Q
        ( left-map-span-diagram 𝒮 s)))

  left-equiv-equiv-descent-data-pushout-function-family :
    (a : domain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( horizontal-map-cocone _ _ c a) →
      family-cocone-family-with-descent-data-pushout Q
        ( horizontal-map-cocone _ _ c a)) ≃
    ( left-family-family-with-descent-data-pushout P a →
      left-family-family-with-descent-data-pushout Q a)
  left-equiv-equiv-descent-data-pushout-function-family a =
    ( equiv-postcomp
      ( left-family-family-with-descent-data-pushout P a)
      ( left-equiv-family-with-descent-data-pushout Q a)) ∘e
    ( equiv-precomp
      ( inv-equiv (left-equiv-family-with-descent-data-pushout P a))
      ( family-cocone-family-with-descent-data-pushout Q
        ( horizontal-map-cocone _ _ c a)))

  right-equiv-equiv-descent-data-pushout-function-family :
    (b : codomain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( vertical-map-cocone _ _ c b) →
      family-cocone-family-with-descent-data-pushout Q
        ( vertical-map-cocone _ _ c b)) ≃
    ( right-family-family-with-descent-data-pushout P b →
      right-family-family-with-descent-data-pushout Q b)
  right-equiv-equiv-descent-data-pushout-function-family b =
    ( equiv-postcomp
      ( right-family-family-with-descent-data-pushout P b)
      ( right-equiv-family-with-descent-data-pushout Q b)) ∘e
    ( equiv-precomp
      ( inv-equiv (right-equiv-family-with-descent-data-pushout P b))
      ( family-cocone-family-with-descent-data-pushout Q
        ( vertical-map-cocone _ _ c b)))

  coherence-equiv-descent-data-pushout-function-family :
    (s : spanning-type-span-diagram 𝒮) →
    coherence-square-maps
      ( map-equiv
        ( left-equiv-equiv-descent-data-pushout-function-family
          ( left-map-span-diagram 𝒮 s)))
      ( tr
        ( family-cocone-family-with-descent-data-pushout-function-family)
        ( coherence-square-cocone _ _ c s))
      ( map-family-descent-data-pushout descent-data-pushout-function-family s)
      ( map-equiv
        ( right-equiv-equiv-descent-data-pushout-function-family
          ( right-map-span-diagram 𝒮 s)))
  coherence-equiv-descent-data-pushout-function-family s =
    ( ( map-equiv
        ( right-equiv-equiv-descent-data-pushout-function-family
          ( right-map-span-diagram 𝒮 s)) ·l
      ( tr-function-type
        ( family-cocone-family-with-descent-data-pushout P)
        ( family-cocone-family-with-descent-data-pushout Q)
        ( coherence-square-cocone _ _ c s)))) ∙h
    ( λ h →
      eq-htpy
        ( horizontal-concat-htpy
          ( coherence-family-with-descent-data-pushout Q s ·r h)
          ( coherence-square-maps-inv-equiv
            ( equiv-tr
              ( family-cocone-family-with-descent-data-pushout P)
              ( coherence-square-cocone _ _ c s))
            ( left-equiv-family-with-descent-data-pushout P
              ( left-map-span-diagram 𝒮 s))
            ( right-equiv-family-with-descent-data-pushout P
              ( right-map-span-diagram 𝒮 s))
            ( equiv-family-family-with-descent-data-pushout P s)
            ( inv-htpy (coherence-family-with-descent-data-pushout P s)))))

  equiv-descent-data-pushout-function-family :
    equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout-function-family))
      ( descent-data-pushout-function-family)
  pr1 equiv-descent-data-pushout-function-family =
    left-equiv-equiv-descent-data-pushout-function-family
  pr1 (pr2 equiv-descent-data-pushout-function-family) =
    right-equiv-equiv-descent-data-pushout-function-family
  pr2 (pr2 equiv-descent-data-pushout-function-family) =
    coherence-equiv-descent-data-pushout-function-family

  family-with-descent-data-pushout-function-family :
    family-with-descent-data-pushout c (l5 ⊔ l6)
  pr1 family-with-descent-data-pushout-function-family =
    family-cocone-family-with-descent-data-pushout-function-family
  pr1 (pr2 family-with-descent-data-pushout-function-family) =
    descent-data-pushout-function-family
  pr2 (pr2 family-with-descent-data-pushout-function-family) =
    equiv-descent-data-pushout-function-family

  compute-section-descent-data-pushout-function-family :
    section-descent-data-pushout descent-data-pushout-function-family ≃
    hom-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout Q)
  compute-section-descent-data-pushout-function-family =
    ( map-underlying-equiv ,
      is-equiv-compute-section-descent-data-pushout-function-family)
    where
    underlying-equiv :
      section-descent-data-pushout descent-data-pushout-function-family ≃
      hom-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout Q)
    underlying-equiv =
      equiv-tot
        ( λ tA →
          equiv-tot
            ( λ tB →
              equiv-Π-equiv-family
                ( λ s →
                  ( equiv-inv-htpy _ _) ∘e
                  ( inv-equiv
                    ( equiv-coherence-triangle-maps-inv-top'
                      ( ( map-family-family-with-descent-data-pushout Q s) ∘
                        ( tA (left-map-span-diagram 𝒮 s)))
                      ( tB (right-map-span-diagram 𝒮 s))
                      ( equiv-family-family-with-descent-data-pushout P s))) ∘e
                  ( equiv-funext))))
    map-underlying-equiv = map-equiv underlying-equiv
    abstract
      is-equiv-compute-section-descent-data-pushout-function-family :
        is-equiv map-underlying-equiv
      is-equiv-compute-section-descent-data-pushout-function-family =
        is-equiv-map-equiv underlying-equiv

  map-compute-section-descent-data-pushout-function-family :
    section-descent-data-pushout descent-data-pushout-function-family →
    hom-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout Q)
  map-compute-section-descent-data-pushout-function-family =
    map-equiv compute-section-descent-data-pushout-function-family

  module _
    (up-c : universal-property-pushout _ _ c)
    (m :
      hom-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout Q))
    where

    abstract
      uniqueness-map-hom-descent-data-pushout :
        is-contr
          ( Σ ( (x : X) →
                family-cocone-family-with-descent-data-pushout P x →
                family-cocone-family-with-descent-data-pushout Q x)
              ( λ h →
                htpy-hom-descent-data-pushout
                  ( descent-data-family-with-descent-data-pushout P)
                  ( descent-data-family-with-descent-data-pushout Q)
                  ( map-compute-section-descent-data-pushout-function-family
                    ( section-descent-data-section-family-cocone-span-diagram
                      ( family-with-descent-data-pushout-function-family)
                      ( h)))
                  ( m)))
      uniqueness-map-hom-descent-data-pushout =
        is-contr-equiv'
          ( fiber
            ( ( map-compute-section-descent-data-pushout-function-family) ∘
              ( section-descent-data-section-family-cocone-span-diagram
                ( family-with-descent-data-pushout-function-family)))
            ( m))
          ( equiv-tot
            ( λ h →
              extensionality-hom-descent-data-pushout
                ( descent-data-family-with-descent-data-pushout P)
                ( descent-data-family-with-descent-data-pushout Q)
                ( _)
                ( m)))
          ( is-contr-map-is-equiv
            ( is-equiv-comp _ _
              ( is-equiv-section-descent-data-section-family-cocone-span-diagram
                ( family-with-descent-data-pushout-function-family)
                ( up-c))
              ( is-equiv-map-equiv
                ( compute-section-descent-data-pushout-function-family)))
            ( m))

    map-hom-descent-data-pushout :
      (x : X) →
      family-cocone-family-with-descent-data-pushout P x →
      family-cocone-family-with-descent-data-pushout Q x
    map-hom-descent-data-pushout =
      pr1 (center uniqueness-map-hom-descent-data-pushout)

    compute-left-map-hom-descent-data-pushout :
      (a : domain-span-diagram 𝒮) →
      coherence-square-maps
        ( left-map-family-with-descent-data-pushout P a)
        ( map-hom-descent-data-pushout (horizontal-map-cocone _ _ c a))
        ( left-map-hom-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout Q)
          ( m)
          ( a))
        ( left-map-family-with-descent-data-pushout Q a)
    compute-left-map-hom-descent-data-pushout a =
      map-inv-equiv
        ( equiv-coherence-triangle-maps-inv-top'
          ( left-map-family-with-descent-data-pushout Q a ∘
            map-hom-descent-data-pushout (horizontal-map-cocone _ _ c a))
          ( left-map-hom-descent-data-pushout
            ( descent-data-family-with-descent-data-pushout P)
            ( descent-data-family-with-descent-data-pushout Q)
            ( m)
            ( a))
          ( left-equiv-family-with-descent-data-pushout P a))
        ( pr1 (pr2 (center uniqueness-map-hom-descent-data-pushout)) a)

    compute-right-map-hom-descent-data-pushout :
      (b : codomain-span-diagram 𝒮) →
      coherence-square-maps
        ( right-map-family-with-descent-data-pushout P b)
        ( map-hom-descent-data-pushout (vertical-map-cocone _ _ c b))
        ( right-map-hom-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout Q)
          ( m)
          ( b))
        ( right-map-family-with-descent-data-pushout Q b)
    compute-right-map-hom-descent-data-pushout b =
      map-inv-equiv
        ( equiv-coherence-triangle-maps-inv-top'
          ( right-map-family-with-descent-data-pushout Q b ∘
            map-hom-descent-data-pushout (vertical-map-cocone _ _ c b))
          ( right-map-hom-descent-data-pushout
            ( descent-data-family-with-descent-data-pushout P)
            ( descent-data-family-with-descent-data-pushout Q)
            ( m)
            ( b))
          ( right-equiv-family-with-descent-data-pushout P b))
        ( pr1 (pr2 (pr2 (center uniqueness-map-hom-descent-data-pushout))) b)
```
