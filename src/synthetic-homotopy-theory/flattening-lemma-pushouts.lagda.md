# The flattening lemma for pushouts

```agda
module synthetic-homotopy-theory.flattening-lemma-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.constant-type-families
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **flattening lemma** for [pushouts](synthetic-homotopy-theory.pushouts.md)
states that pushouts commute with
[dependent pair types](foundation.dependent-pair-types.md). More precisely,
given a pushout square

```text
      g
  S -----> B
  |        |
 f|        |j
  V        V
  A -----> X
      i
```

with homotopy `H : i ∘ f ~ j ∘ g`, and for any type family `P` over `X`, the
commuting square

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           V                                                 V
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x)
```

is again a pushout square.

## Definitions

### The statement of the flattening lemma

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {X : UU l4} (P : X → UU l5)
  (f : S → A) (g : S → B) (c : cocone f g X)
  (dup-pushout : {l : Level} → dependent-universal-property-pushout l f g c)
  where

  horizontal-map-cocone-flattening-pushout :
    Σ A (P ∘ horizontal-map-cocone f g c) → Σ X P
  horizontal-map-cocone-flattening-pushout =
    map-Σ-map-base (horizontal-map-cocone f g c) P

  vertical-map-cocone-flattening-pushout :
    Σ B (P ∘ vertical-map-cocone f g c) → Σ X P
  vertical-map-cocone-flattening-pushout =
    map-Σ-map-base (vertical-map-cocone f g c) P

  coherence-square-cocone-flattening-pushout :
    coherence-square-maps
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( vertical-map-cocone-flattening-pushout)
      ( horizontal-map-cocone-flattening-pushout)
  coherence-square-cocone-flattening-pushout =
    coherence-square-maps-map-Σ-map-base P g f
      ( vertical-map-cocone f g c)
      ( horizontal-map-cocone f g c)
      ( coherence-square-cocone f g c)

  coherence-square-cocone-flattening-pushout' :
    coherence-square-maps
      ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c))
      ( map-Σ
        ( P ∘ horizontal-map-cocone f g c)
        ( f)
        ( λ s → tr P (inv (coherence-square-cocone f g c s))))
      ( vertical-map-cocone-flattening-pushout)
      ( horizontal-map-cocone-flattening-pushout)
  coherence-square-cocone-flattening-pushout' =
    coherence-square-maps-map-Σ-map-base' P g f
      ( vertical-map-cocone f g c)
      ( horizontal-map-cocone f g c)
      ( coherence-square-cocone f g c)

  cocone-flattening-pushout :
    cocone
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( Σ X P)
  pr1 cocone-flattening-pushout =
    horizontal-map-cocone-flattening-pushout
  pr1 (pr2 cocone-flattening-pushout) =
    vertical-map-cocone-flattening-pushout
  pr2 (pr2 cocone-flattening-pushout) =
    coherence-square-cocone-flattening-pushout

  cocone-map-flattening-pushout :
    { l : Level} (Y : UU l) →
    ( Σ X P → Y) →
    cocone
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( Y)
  cocone-map-flattening-pushout Y =
    cocone-map
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( cocone-flattening-pushout)

  cocone-flattening-pushout' :
    cocone
      ( map-Σ
        ( P ∘ horizontal-map-cocone f g c)
        ( f)
        ( λ s → tr P (inv (coherence-square-cocone f g c s))))
      ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c))
      ( Σ X P)
  pr1 cocone-flattening-pushout' =
    horizontal-map-cocone-flattening-pushout
  pr1 (pr2 cocone-flattening-pushout') =
    vertical-map-cocone-flattening-pushout
  pr2 (pr2 cocone-flattening-pushout') =
    coherence-square-cocone-flattening-pushout'

  cocone-map-flattening-pushout' :
    { l : Level} (Y : UU l) →
    ( Σ X P → Y) →
    cocone
      ( map-Σ
        ( P ∘ horizontal-map-cocone f g c)
        ( f)
        ( λ s → tr P (inv (coherence-square-cocone f g c s))))
      ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c))
      ( Y)
  cocone-map-flattening-pushout' Y =
    cocone-map
      ( map-Σ
        ( P ∘ horizontal-map-cocone f g c)
        ( f)
        ( λ s → tr P (inv (coherence-square-cocone f g c s))))
      ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c))
      ( cocone-flattening-pushout')

  flattening-lemma-statement : UUω
  flattening-lemma-statement =
    {l : Level} →
    universal-property-pushout l
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( cocone-flattening-pushout)

  UωU : UUω₁
  UωU = UUω

  flattening-lemma-statement' : UωU
  flattening-lemma-statement' =
    {l : Level} →
    universal-property-pushout l
      ( map-Σ
        ( P ∘ horizontal-map-cocone f g c)
        ( f)
        ( λ s → tr P (inv (coherence-square-cocone f g c s))))
      ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c))
      ( cocone-flattening-pushout')

  comparison-coherence-dependent-cocone-htpy' :
    { l : Level} (Y : UU l) →
    { i : S → X} {j : S → X} (H : i ~ j) →
    ( k : (s : S) → P (i s) → Y) →
    ( l : (s : S) → P (j s) → Y) →
    ( s : S) →
    ( k s ~ (l s ∘ tr P (H s) )) ≃
    ( dependent-identification
      ( λ x → P x → Y)
      ( H s)
      ( k s)
      ( l s))
  comparison-coherence-dependent-cocone-htpy' Y {i = i} =
    ind-htpy i
      ( λ j H →
        ( k : (s : S) → P (i s) → Y) →
        ( l : (s : S) → P (j s) → Y) →
        ( s : S) →
        ( k s ~ (l s ∘ tr P (H s) )) ≃
        ( dependent-identification
          ( λ x → P x → Y)
          ( H s)
          ( k s)
          ( l s)))
      ( λ k l s → inv-equiv (equiv-funext))

  compute-comparison-coherence-dependent-cocone-htpy' :
    { l : Level} (Y : UU l) →
    { i : S → X} {j : S → X} (H : i ~ j) →
    ( s : S) →
    ( h : (x : X) → P x → Y) →
    ( map-equiv
      ( comparison-coherence-dependent-cocone-htpy' Y H (h ∘ i) (h ∘ j) s)
      ( λ t → ap (ind-Σ h) (eq-pair-Σ (H s) refl))) ＝
    apd h (H s)
  compute-comparison-coherence-dependent-cocone-htpy' Y {i = i} H s h =
    ind-htpy i
      ( λ j H →
        ( s : S) →
        ( h : (x : X) → P x → Y) →
        ( map-equiv
          ( comparison-coherence-dependent-cocone-htpy' Y H (h ∘ i) (h ∘ j) s)
          ( λ t → ap (ind-Σ h) (eq-pair-Σ (H s) refl))) ＝
        apd h (H s))
      ( λ s h →
         ( ap
          ( λ f → map-equiv (f (h ∘ i) (h ∘ i) s) refl-htpy)
          ( compute-ind-htpy i
            ( λ j H →
              ( k : (s : S) → P (i s) → Y) →
              ( l : (s : S) → P (j s) → Y) →
              ( s : S) →
              ( k s ~ (l s ∘ tr P (H s) )) ≃
              ( dependent-identification
                ( λ x → P x → Y)
                ( H s)
                ( k s)
                ( l s)))
            ( λ k l s → inv-equiv (equiv-funext)))) ∙
          ( eq-htpy-refl-htpy (h (i s))))
      ( H)
      ( s)
      ( h)

  comparison-coherence-dependent-cocone-htpy :
    { l : Level} (Y : UU l) →
    ( k' : (s : S) → P (horizontal-map-cocone f g c (f s)) → Y) →
    ( l' : (s : S) → P (vertical-map-cocone f g c (g s)) → Y) →
    ( s : S) →
    ( dependent-identification
      ( λ x → P x → Y)
      ( coherence-square-cocone f g c s)
      ( k' s)
      ( l' s)) ≃
    ( k' s ~ (l' s ∘ tr P (coherence-square-cocone f g c s) ))
  comparison-coherence-dependent-cocone-htpy Y k' l' s =
    equiv-Π-equiv-family
      ( λ t →
        equiv-concat'
          ( k' s t)
          ( ( tr-constant-type-family
             ( inv (coherence-square-cocone f g c s))
             ( l' s
               ( tr P
                 ( inv (inv (coherence-square-cocone f g c s)))
                 ( t)))) ∙
            ( ap
              ( λ p → l' s (tr P p t))
              ( inv-inv (coherence-square-cocone f g c s))))) ∘e
    equiv-funext ∘e
    equiv-concat'
      ( k' s)
      ( tr-function-type P
        ( λ _ → Y)
        ( inv (coherence-square-cocone f g c s))
        ( l' s)) ∘e
    eq-transpose-equiv
      ( equiv-tr
        ( λ x → P x → Y)
        ( coherence-square-cocone f g c s))
      ( k' s)
      ( l' s)

  comparison-dependent-cocone-ind-Σ-cocone :
    {l : Level} (Y : UU l) →
    Σ ( (a : A) → P (horizontal-map-cocone f g c a) → Y)
      ( λ k →
        Σ ( (b : B) → P (vertical-map-cocone f g c b) → Y)
          ( λ l →
            ( s : S) (t : P (horizontal-map-cocone f g c (f s))) →
            ( k (f s) t) ＝
            ( l (g s) (tr P (coherence-square-cocone f g c s) t)))) ≃
    dependent-cocone f g c (λ x → P x → Y)
  comparison-dependent-cocone-ind-Σ-cocone Y =
    equiv-tot
      ( λ k →
        equiv-tot
          ( λ l →
            equiv-Π-equiv-family
              ( comparison-coherence-dependent-cocone-htpy' Y
                ( coherence-square-cocone f g c)
                ( k ∘ f)
                ( l ∘ g))))
              -- ( comparison-coherence-dependent-cocone-htpy Y (k ∘ f) (l ∘ g))))

  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    {l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-map f g c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-pushout Y ∘ ind-Σ)
    -- coherence-square-maps
    --   ( cocone-map-flattening-pushout Y ∘ ind-Σ)
    --   ( dependent-cocone-map f g c (λ x → P x → Y))
    --   ( map-equiv equiv-ev-pair³)
    --   ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
  triangle-comparison-dependent-cocone-ind-Σ-cocone Y h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( eq-htpy
          ( λ s →
            inv
              ( compute-comparison-coherence-dependent-cocone-htpy' Y
                ( coherence-square-cocone f g c)
                ( s)
                ( h) ))))

  comparison-ind-Σ-cocone-dependent-cocone' :
    { l : Level} (Y : UU l) →
    Σ ( (a : A) → P (horizontal-map-cocone f g c a) → Y)
      ( λ k →
        Σ ( (b : B) → P (vertical-map-cocone f g c b) → Y)
          ( λ l →
            ( s : S) (t : P (vertical-map-cocone f g c (g s))) →
            k (f s) (tr P (inv (coherence-square-cocone f g c s)) t) ＝
            l (g s) t)) ≃
    dependent-cocone f g c (λ x → P x → Y)
  comparison-ind-Σ-cocone-dependent-cocone' Y =
    equiv-tot
      ( λ k →
        equiv-tot
        ( λ l →
          equiv-Π-equiv-family
            ( λ s →
              ( equiv-concat
                ( tr-function-type
                  ( P)
                  ( λ _ → Y)
                  ( coherence-square-cocone f g c s)
                  ( k (f s)))
                ( l (g s))) ∘e
              ( ( inv-equiv equiv-funext) ∘e
                ( equiv-Π-equiv-family
                  ( λ t →
                    equiv-concat
                      ( tr-constant-type-family
                        ( coherence-square-cocone f g c s)
                        ( k
                          ( f s)
                          ( tr P (inv (coherence-square-cocone f g c s)) t)))
                      ( l (g s) t)))))))

  flattening-lemma-pushout' : flattening-lemma-statement'
  flattening-lemma-pushout' Y =
    is-equiv-left-factor
      ( cocone-map-flattening-pushout' Y)
      ( ind-Σ)
      ( is-equiv-right-factor-htpy
        ( dependent-cocone-map f g c (λ x → P x → Y))
        ( map-equiv
          ( comparison-ind-Σ-cocone-dependent-cocone' Y ∘e equiv-ev-pair³))
        ( cocone-map-flattening-pushout' Y ∘ ind-Σ)
        ( λ h →
          eq-pair-Σ
            ( refl)
            ( eq-pair-Σ
              ( refl)
              ( eq-htpy
                ( λ s →
                  compute-apd-fiberwise-constant-codomain
                    ( h)
                    ( coherence-square-cocone f g c s)))))
        ( is-equiv-map-equiv
          ( comparison-ind-Σ-cocone-dependent-cocone' Y ∘e equiv-ev-pair³))
        ( dup-pushout (λ x → P x → Y)))
      ( is-equiv-ind-Σ)

  flattening-lemma-pushout : flattening-lemma-statement
  flattening-lemma-pushout {l} Y =
    tr
      ( λ co →
        is-equiv
          ( cocone-map
            ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
            ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c) ∘
              tot (λ s → tr P (coherence-square-cocone f g c s)))
            { Y = Y}
            ( co)))
      ( [iv])
      ( [iii])
    where
    [i] :
      cocone
        ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c ))
        ( tot (λ s → tr P (coherence-square-cocone f g c s)))
        ( Σ A (P ∘ horizontal-map-cocone f g c))
    pr1 [i] = id
    pr1 (pr2 [i]) =
      map-Σ
        ( P ∘ horizontal-map-cocone f g c)
        ( f)
        ( λ s → tr P (inv (coherence-square-cocone f g c s)))
    pr2 (pr2 [i]) st =
      eq-pair-Σ
        ( refl)
        ( inv
          ( is-retraction-map-inv-equiv
            ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
            ( pr2 st)))
    [ii] :
      {l : Level} →
      universal-property-pushout
        ( l)
        ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c ))
        ( tot (λ s → tr P (coherence-square-cocone f g c s)))
        ( [i])
    [ii] =
      universal-property-pushout-is-equiv'
        ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
        ( tot (λ s → tr P (coherence-square-cocone f g c s)))
        ( [i])
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ s →
            is-equiv-tr P (coherence-square-cocone f g c s)))
        is-equiv-id
    [iii] =
      universal-property-pushout-rectangle-universal-property-pushout-right
        ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
        ( tot (λ s → tr P (coherence-square-cocone f g c s)))
        ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c))
        ( [i])
        ( cocone-flattening-pushout')
        ( [ii])
        ( flattening-lemma-pushout')
        Y
    [iv] :
      cocone-comp-horizontal
        ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
        ( tot (λ s → tr P (coherence-square-cocone f g c s)))
        ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c))
        ( [i])
        ( cocone-flattening-pushout') ＝
      cocone-flattening-pushout
    [iv] =
      eq-htpy-cocone
        ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
        ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c) ∘
          tot (λ s → tr P (coherence-square-cocone f g c s)))
        ( cocone-comp-horizontal
          ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
          ( tot (λ s → tr P (coherence-square-cocone f g c s)))
          ( map-Σ-map-base g (P ∘ vertical-map-cocone f g c))
          ( [i])
          ( cocone-flattening-pushout'))
        ( cocone-flattening-pushout)
        ( refl-htpy ,
          refl-htpy ,
          ( λ st →
            right-unit ∙
            ( equational-reasoning
              ( ( ap
                  ( map-Σ-map-base (horizontal-map-cocone f g c) P)
                  ( eq-pair-Σ
                    ( refl)
                    ( inv
                      ( is-retraction-map-inv-equiv
                        ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                        ( pr2 st))))) ∙
                ( eq-pair-Σ
                  ( coherence-square-cocone f g c (pr1 st))
                  ( is-section-map-inv-equiv
                    ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                    ( tr P (coherence-square-cocone f g c (pr1 st)) (pr2 st)))))
              ＝ eq-pair-Σ
                  ( refl)
                  ( ap (λ t → t)
                    ( inv
                    ( is-retraction-map-inv-equiv
                      ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                      (pr2 st)))) ∙
                eq-pair-Σ
                  ( coherence-square-cocone f g c (pr1 st))
                  ( is-section-map-inv-equiv
                    ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                    ( tr P (coherence-square-cocone f g c (pr1 st)) (pr2 st)))
                by
                ap-binary
                  (  _∙_)
                  ( compute-ap-map-Σ-eq-pair-Σ
                    ( horizontal-map-cocone f g c)
                    ( λ _ t → t)
                    ( refl)
                    ( inv
                      ( is-retraction-map-inv-equiv
                        ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                        ( pr2 st))))
                  ( refl)
              ＝ eq-pair-Σ
                  ( refl)
                  ( inv
                    ( is-retraction-map-inv-equiv
                      ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                      (pr2 st))) ∙
                eq-pair-Σ
                  ( coherence-square-cocone f g c (pr1 st))
                  ( is-section-map-inv-equiv
                    ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                    ( tr P (coherence-square-cocone f g c (pr1 st)) (pr2 st)))
                by
                ap-binary
                  ( λ p q → eq-pair-Σ refl p ∙ q)
                  ( ap-id
                    ( inv
                        ( is-retraction-map-inv-equiv
                          ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                          ( pr2 st))))
                  ( refl)
              ＝ eq-pair-Σ
                  ( coherence-square-cocone f g c (pr1 st))
                  ( concat-dependent-identification
                    ( P)
                    ( refl)
                    ( coherence-square-cocone f g c (pr1 st))
                    ( inv
                      ( is-retraction-map-inv-equiv
                        ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                        ( pr2 st)))
                    ( is-section-map-inv-equiv
                      ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                      ( tr
                        ( P)
                        ( coherence-square-cocone f g c (pr1 st))
                        ( pr2 st))))
                by
                inv
                  ( interchange-concat-eq-pair-Σ
                    ( refl)
                    ( coherence-square-cocone f g c (pr1 st))
                    ( inv
                      ( is-retraction-map-inv-equiv
                        ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                        ( pr2 st)))
                    ( is-section-map-inv-equiv
                      ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                      ( tr
                        ( P)
                        ( coherence-square-cocone f g c (pr1 st))
                        ( pr2 st))))
              ＝ eq-pair-Σ (coherence-square-cocone f g c (pr1 st)) refl
                by
                ap
                  ( eq-pair-Σ
                    ( coherence-square-cocone f g c (pr1 st)))
                  ( compute-concat-dependent-identification-refl
                    ( P)
                    ( coherence-square-cocone f g c (pr1 st))
                    ( inv
                      ( is-retraction-map-inv-equiv
                        ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                        ( pr2 st)))
                    ( is-section-map-inv-equiv
                      ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                      ( tr
                        ( P)
                        ( coherence-square-cocone f g c (pr1 st))
                        ( pr2 st))) ∙
                    ( ( ap-binary
                        ( _∙_)
                        ( ap-inv
                            ( tr P (coherence-square-cocone f g c (pr1 st)))
                            ( is-retraction-map-inv-equiv
                              ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                              ( pr2 st)))
                        ( refl) ∙
                        inv
                          ( left-transpose-eq-concat
                            ( ap
                              ( tr P (coherence-square-cocone f g c (pr1 st)))
                              ( is-retraction-map-inv-equiv
                                ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                                ( pr2 st)))
                            ( refl)
                            ( is-section-map-inv-equiv
                              ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                              ( tr P (coherence-square-cocone f g c (pr1 st)) (pr2 st)))
                            ( inv
                              ( coherence-map-inv-equiv
                                ( equiv-tr P (coherence-square-cocone f g c (pr1 st)))
                                ( pr2 st) ∙
                              inv right-unit)))) )))))

  flattening-lemma-original : flattening-lemma-statement
  flattening-lemma-original Y =
    is-equiv-left-factor
      ( cocone-map-flattening-pushout Y)
      ( ind-Σ)
      ( is-equiv-right-factor
        ( map-equiv equiv-ev-pair³)
        ( cocone-map-flattening-pushout Y ∘ ind-Σ)
        ( is-equiv-map-equiv equiv-ev-pair³)
        ( is-equiv-right-factor-htpy
          ( dependent-cocone-map f g c (λ x → P x → Y))
          ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
          ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-pushout Y ∘ ind-Σ)
          ( triangle-comparison-dependent-cocone-ind-Σ-cocone Y)
          ( is-equiv-map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
          ( dup-pushout (λ x → P x → Y))))
      ( is-equiv-ind-Σ)
```
