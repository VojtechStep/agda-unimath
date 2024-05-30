# Sections of descent data for pushouts

```agda
module synthetic-homotopy-theory.sections-descent-data-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

## Definitions

### Sections of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4)
  where

  section-descent-data-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  section-descent-data-pushout =
    Σ ( (a : domain-span-diagram 𝒮) → left-family-descent-data-pushout P a)
      ( λ tA →
        Σ ( (b : codomain-span-diagram 𝒮) →
            right-family-descent-data-pushout P b)
          ( λ tB →
            (s : spanning-type-span-diagram 𝒮) →
            map-family-descent-data-pushout P s
              ( tA (left-map-span-diagram 𝒮 s)) ＝
            tB (right-map-span-diagram 𝒮 s)))
```

### Homotopies of sections of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4)
  (r t : section-descent-data-pushout P)
  where

  htpy-section-descent-data-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-descent-data-pushout =
    Σ ( pr1 r ~ pr1 t)
      ( λ HA →
        Σ (pr1 (pr2 r) ~ pr1 (pr2 t))
          ( λ HB →
            (s : spanning-type-span-diagram 𝒮) →
            coherence-square-identifications
              ( ap
                ( map-family-descent-data-pushout P s)
                ( HA (left-map-span-diagram 𝒮 s)))
              ( pr2 (pr2 r) s)
              ( pr2 (pr2 t) s)
              ( HB (right-map-span-diagram 𝒮 s))))
```

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4)
  (r : section-descent-data-pushout P)
  where

  refl-htpy-section-descent-data-pushout :
    htpy-section-descent-data-pushout P r r
  pr1 refl-htpy-section-descent-data-pushout = refl-htpy
  pr1 (pr2 refl-htpy-section-descent-data-pushout) = refl-htpy
  pr2 (pr2 refl-htpy-section-descent-data-pushout) = right-unit-htpy
```

## Properties

### Characterization of identity types of sections of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4)
  (r : section-descent-data-pushout P)
  where

  htpy-eq-section-descent-data-pushout :
    (t : section-descent-data-pushout P) →
    (r ＝ t) → htpy-section-descent-data-pushout P r t
  htpy-eq-section-descent-data-pushout .r refl =
    refl-htpy-section-descent-data-pushout P r

  abstract
    is-torsorial-htpy-section-descent-data-pushout :
      is-torsorial (htpy-section-descent-data-pushout P r)
    is-torsorial-htpy-section-descent-data-pushout =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (pr1 r))
        ( pr1 r , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy (pr1 (pr2 r)))
          ( pr1 (pr2 r) , refl-htpy)
          ( is-torsorial-htpy (pr2 (pr2 r) ∙h refl-htpy)))

  is-equiv-htpy-eq-section-descent-data-pushout :
    (t : section-descent-data-pushout P) →
    is-equiv (htpy-eq-section-descent-data-pushout t)
  is-equiv-htpy-eq-section-descent-data-pushout =
    fundamental-theorem-id
      ( is-torsorial-htpy-section-descent-data-pushout)
      ( htpy-eq-section-descent-data-pushout)

  extensionality-section-descent-data-pushout :
    (t : section-descent-data-pushout P) →
    (r ＝ t) ≃ htpy-section-descent-data-pushout P r t
  pr1 (extensionality-section-descent-data-pushout t) =
    htpy-eq-section-descent-data-pushout t
  pr2 (extensionality-section-descent-data-pushout t) =
    is-equiv-htpy-eq-section-descent-data-pushout t
```

### Sections of families over a pushout correspond to sections of the corresponding descent data

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5)
  where

  section-descent-data-section-family-cocone-span-diagram :
    ((x : X) → family-cocone-family-with-descent-data-pushout P x) →
    section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
  pr1 (section-descent-data-section-family-cocone-span-diagram f) a =
    left-map-family-with-descent-data-pushout P a
      ( f (horizontal-map-cocone _ _ c a))
  pr1 (pr2 (section-descent-data-section-family-cocone-span-diagram f)) b =
    right-map-family-with-descent-data-pushout P b
      ( f (vertical-map-cocone _ _ c b))
  pr2 (pr2 (section-descent-data-section-family-cocone-span-diagram f)) s =
    ( inv
      ( coherence-family-with-descent-data-pushout P s
        ( f (horizontal-map-cocone _ _ c (left-map-span-diagram 𝒮 s))))) ∙
    ( ap
      ( right-map-family-with-descent-data-pushout P
        ( right-map-span-diagram 𝒮 s))
      ( apd f (coherence-square-cocone _ _ c s)))

  equiv-[i] :
    dependent-cocone-span-diagram c
      ( family-cocone-family-with-descent-data-pushout P) ≃
    section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
  equiv-[i] =
    ( map-underlying-equiv ,
      is-equiv-[i])
    where
    underlying-equiv =
      equiv-Σ _
        ( equiv-Π-equiv-family (left-equiv-family-with-descent-data-pushout P))
        ( λ sA →
          equiv-Σ _
            ( equiv-Π-equiv-family
              ( right-equiv-family-with-descent-data-pushout P))
            ( λ sB →
              equiv-Π-equiv-family
                ( λ s →
                  ( equiv-inv-concat
                    ( coherence-family-with-descent-data-pushout P s
                      ( sA (left-map-span-diagram 𝒮 s)))
                    ( _)) ∘e
                  ( equiv-ap-emb
                    ( emb-equiv
                      ( right-equiv-family-with-descent-data-pushout P
                        ( right-map-span-diagram 𝒮 s)))))))
    map-underlying-equiv = map-equiv underlying-equiv
    abstract
      is-equiv-[i] : is-equiv map-underlying-equiv
      is-equiv-[i] = is-equiv-map-equiv underlying-equiv

  triangle-[i] :
    coherence-triangle-maps
      ( section-descent-data-section-family-cocone-span-diagram)
      ( map-equiv equiv-[i])
      ( dependent-cocone-map-span-diagram c
        ( family-cocone-family-with-descent-data-pushout P))
  triangle-[i] = refl-htpy

  abstract
    is-equiv-section-descent-data-section-family-cocone-span-diagram :
      universal-property-pushout _ _ c →
      is-equiv (section-descent-data-section-family-cocone-span-diagram)
    is-equiv-section-descent-data-section-family-cocone-span-diagram up-c =
      is-equiv-left-map-triangle
        ( section-descent-data-section-family-cocone-span-diagram)
        ( map-equiv equiv-[i])
        ( dependent-cocone-map-span-diagram c (family-cocone-family-with-descent-data-pushout P))
        ( triangle-[i])
        ( dependent-universal-property-universal-property-pushout _ _ _ up-c
          ( family-cocone-family-with-descent-data-pushout P))
        ( is-equiv-map-equiv equiv-[i])

  asdf :
    universal-property-pushout _ _ c →
    ((x : X) → family-cocone-family-with-descent-data-pushout P x) ≃
    section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
  pr1 (asdf _) =
    section-descent-data-section-family-cocone-span-diagram
  pr2 (asdf up-c) =
    is-equiv-section-descent-data-section-family-cocone-span-diagram up-c
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : family-with-descent-data-pushout c l5)
  (t :
    section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P))
  where

  abstract
    uniqueness-section-family-section-descent-data-pushout :
      is-contr
        ( Σ ( (x : X) → family-cocone-family-with-descent-data-pushout P x)
            ( λ h →
              htpy-section-descent-data-pushout
                ( descent-data-family-with-descent-data-pushout P)
                ( section-descent-data-section-family-cocone-span-diagram P h)
                ( t)))
    uniqueness-section-family-section-descent-data-pushout =
      is-contr-equiv'
        ( fiber (section-descent-data-section-family-cocone-span-diagram P) t)
        ( equiv-tot
          ( λ h →
            extensionality-section-descent-data-pushout
              ( descent-data-family-with-descent-data-pushout P)
              ( _)
              ( t)))
        ( is-contr-map-is-equiv
          ( is-equiv-section-descent-data-section-family-cocone-span-diagram P
            ( up-c))
          ( t))

  section-family-section-descent-data-pushout :
    (x : X) → family-cocone-family-with-descent-data-pushout P x
  section-family-section-descent-data-pushout =
    pr1 (center uniqueness-section-family-section-descent-data-pushout)

  htpy-section-family-section-descent-data-pushout :
    htpy-section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( section-descent-data-section-family-cocone-span-diagram P
        ( section-family-section-descent-data-pushout))
      ( t)
  htpy-section-family-section-descent-data-pushout =
    pr2 (center uniqueness-section-family-section-descent-data-pushout)
```
