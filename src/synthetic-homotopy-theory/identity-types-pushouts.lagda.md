# Identity type of pushouts

```agda
module synthetic-homotopy-theory.identity-types-pushouts where
```

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.sequential-diagrams
```

```agda
module _
  { l : Level} (A : UU l) (B : UU l) (R : A → B → UU l) (a0 : A)
  where

  interleaved mutual
    path-pushout-type-a : ℕ → A → UU l
    path-pushout-type-b : ℕ → B → UU l
    path-pushout-concat-a :
      (t : ℕ) → (a : A) → (b : B) → R a b →
      path-pushout-type-a t a → path-pushout-type-b t b
    path-pushout-concat-b :
      (t : ℕ) → (a : A) → (b : B) → R a b →
      path-pushout-type-b t b → path-pushout-type-a (succ-ℕ t) a

    path-pushout-type-a zero-ℕ a = a0 ＝ a
    path-pushout-type-a (succ-ℕ t) a =
      pushout
        { S = Σ B (λ b → R a b × path-pushout-type-a t a)}
        ( pr2 ∘ pr2)
        ( tot (λ b → tot (path-pushout-concat-a t a b)))

    path-pushout-type-b zero-ℕ b = R a0 b
    path-pushout-type-b (succ-ℕ t) b =
      pushout
        { S = Σ A (λ a → R a b × path-pushout-type-b t b)}
        ( pr2 ∘ pr2)
        ( tot (λ a → tot (path-pushout-concat-b t a b)))

    path-pushout-concat-a zero-ℕ a b r refl = r
    path-pushout-concat-a (succ-ℕ t) a b r p =
      inr-pushout
        { S = Σ A (λ a → R a b × path-pushout-type-b t b)}
        ( pr2 ∘ pr2)
        ( tot (λ a → tot (path-pushout-concat-b t a b)))
        ( a , r , p)

    path-pushout-concat-b t a b r p =
      inr-pushout
        ( pr2 ∘ pr2)
        ( tot (λ b → tot (path-pushout-concat-a t a b)))
        ( b , r , p)

  inject-path-pushout-a : (t : ℕ) → (a : A) →
    path-pushout-type-a t a → path-pushout-type-a (succ-ℕ t) a
  inject-path-pushout-a t a =
    inl-pushout
      ( pr2 ∘ pr2)
      ( tot (λ b → tot (path-pushout-concat-a t a b)))

  inject-path-pushout-b : (t : ℕ) → (b : B) →
    path-pushout-type-b t b → path-pushout-type-b (succ-ℕ t) b
  inject-path-pushout-b t b =
    inl-pushout
      ( pr2 ∘ pr2)
      ( tot (λ a → tot (path-pushout-concat-b t a b)))

  coherence-path-pushout-a : (t : ℕ) → (a : A) → (b : B) → (r : R a b) →
    coherence-triangle-maps
      ( inject-path-pushout-a t a)
      ( path-pushout-concat-b t a b r)
      ( path-pushout-concat-a t a b r)
  coherence-path-pushout-a t a b r p =
    glue-pushout
      ( pr2 ∘ pr2)
      ( tot (λ b → tot (path-pushout-concat-a t a b)))
      ( b , r , p)

  coherence-path-pushout-b : (t : ℕ) → (a : A) → (b : B) → (r : R a b) →
    coherence-triangle-maps
      ( inject-path-pushout-b t b)
      ( path-pushout-concat-a (succ-ℕ t) a b r)
      ( path-pushout-concat-b t a b r)
  coherence-path-pushout-b t a b r p =
    glue-pushout
      ( pr2 ∘ pr2)
      ( tot (λ a → tot (path-pushout-concat-b t a b)))
      ( a , r , p)

  type-stage-path-space-pushout : UU (lsuc l)
  type-stage-path-space-pushout =
    Σ ( A → UU l)
      ( λ path-pushout-type-a' →
        Σ ( B → UU l)
          ( λ path-pushout-type-b' →
            Σ ( ( a : A) (b : B) → R a b →
                ( path-pushout-type-a' a) → (path-pushout-type-b' b))
              ( λ path-pushout-concat-a' →
                ( a : A) (b : B) → R a b →
                ( path-pushout-type-b' b) →
                pushout
                  ( pr2 ∘ pr2)
                  ( tot (λ b → tot (path-pushout-concat-a' a b))))))

  family-first-stage-path-space-pushout :
    type-stage-path-space-pushout → A → UU l
  family-first-stage-path-space-pushout = pr1

  family-second-stage-path-space-pushout :
    type-stage-path-space-pushout → B → UU l
  family-second-stage-path-space-pushout = pr1 ∘ pr2

  concat-first-stage-path-space-pushout :
    ( d : type-stage-path-space-pushout) →
    ( a : A) (b : B) → R a b →
    family-first-stage-path-space-pushout d a →
    family-second-stage-path-space-pushout d b
  concat-first-stage-path-space-pushout = pr1 ∘ pr2 ∘ pr2

  concat-second-stage-path-space-pushout :
    ( d : type-stage-path-space-pushout) →
    ( a : A) (b : B) → R a b →
    family-second-stage-path-space-pushout d b →
    pushout
      ( pr2 ∘ pr2)
      ( tot (λ b → tot (concat-first-stage-path-space-pushout d a b)))
  concat-second-stage-path-space-pushout = pr2 ∘ pr2 ∘ pr2

  path-space-pushout :
    ℕ → type-stage-path-space-pushout
  path-space-pushout zero-ℕ =
    path-pushout-type-a' ,
    path-pushout-type-b' ,
    path-pushout-concat-a' ,
    path-pushout-concat-b'
    where
      path-pushout-type-a' : A → UU l
      path-pushout-type-a' a = a0 ＝ a
      path-pushout-type-b' : B → UU l
      path-pushout-type-b' b = R a0 b
      path-pushout-concat-a' :
        ( a : A) (b : B) → R a b →
        path-pushout-type-a' a → path-pushout-type-b' b
      path-pushout-concat-a' a b r refl = r
      path-pushout-concat-b' :
        ( a : A) (b : B) → R a b →
        path-pushout-type-b' b →
        pushout
          ( pr2 ∘ pr2)
          ( tot (λ b → tot (path-pushout-concat-a' a b)))
      path-pushout-concat-b' a b r p =
        inr-pushout
          ( pr2 ∘ pr2)
          ( tot (λ b → tot (path-pushout-concat-a' a b)))
          ( b , r , p)
  path-space-pushout (succ-ℕ t) =
    path-pushout-type-a' ,
    path-pushout-type-b' ,
    path-pushout-concat-a' ,
    path-pushout-concat-b'
    where
      path-pushout-type-a' : A → UU l
      path-pushout-type-a' a =
        pushout
          ( pr2 ∘ pr2)
          ( tot
            ( λ b →
              tot
                ( concat-first-stage-path-space-pushout
                  ( path-space-pushout t)
                  ( a)
                  ( b))))
      path-pushout-type-b' : B → UU l
      path-pushout-type-b' b =
        pushout
          ( pr2 ∘ pr2)
          ( tot
            ( λ a →
              tot
                ( concat-second-stage-path-space-pushout
                  ( path-space-pushout t)
                  ( a)
                  ( b))))
      path-pushout-concat-a' :
        ( a : A) (b : B) → R a b →
        path-pushout-type-a' a → path-pushout-type-b' b
      path-pushout-concat-a' a b r p =
        inr-pushout
          ( pr2 ∘ pr2)
          ( tot
            ( λ a →
              tot
                ( concat-second-stage-path-space-pushout
                  ( path-space-pushout t)
                  ( a)
                  ( b))))
          ( a , r , p)
      path-pushout-concat-b' :
        ( a : A) (b : B) → R a b →
        path-pushout-type-b' b →
        pushout
          ( pr2 ∘ pr2)
          ( tot (λ b → tot (path-pushout-concat-a' a b)))
      path-pushout-concat-b' a b r p =
        inr-pushout
          ( pr2 ∘ pr2)
          ( tot (λ b → tot (path-pushout-concat-a' a b)))
          ( b , r , p)

  path-pushout-type-a' : A → ℕ → UU l
  path-pushout-type-a' a t =
    family-first-stage-path-space-pushout (path-space-pushout t) a

  path-pushout-type-b' : B → ℕ → UU l
  path-pushout-type-b' b t =
    family-second-stage-path-space-pushout (path-space-pushout t) b

  path-pushout-concat-a' :
    ( a : A) (t : ℕ) (b : B) → R a b →
    path-pushout-type-a' a t → path-pushout-type-b' b t
  path-pushout-concat-a' a t =
    concat-first-stage-path-space-pushout (path-space-pushout t) a

  path-pushout-concat-b' :
    ( b : B) (t : ℕ) (a : A) → R a b →
    path-pushout-type-b' b t → path-pushout-type-a' a (succ-ℕ t)
  path-pushout-concat-b' b t a =
    concat-second-stage-path-space-pushout (path-space-pushout t) a b

  inject-path-pushout-a' :
    ( a : A) (t : ℕ) →
    path-pushout-type-a' a t → path-pushout-type-a' a (succ-ℕ t)
  inject-path-pushout-a' a t =
    inl-pushout
      ( pr2 ∘ pr2)
      ( tot (λ b → tot (path-pushout-concat-a' a t b)))

  inject-path-pushout-b' :
    ( b : B) (t : ℕ) →
    path-pushout-type-b' b t → path-pushout-type-b' b (succ-ℕ t)
  inject-path-pushout-b' b t =
    inl-pushout
      ( pr2 ∘ pr2)
      ( tot (λ a → tot (path-pushout-concat-b' b t a)))

  coherence-path-pushout-a' :
    ( a : A) (t : ℕ) (b : B) (r : R a b) →
    coherence-triangle-maps
      ( inject-path-pushout-a' a t)
      ( path-pushout-concat-b' b t a r)
      ( path-pushout-concat-a' a t b r)
  coherence-path-pushout-a' a zero-ℕ b r p =
    glue-pushout
      ( pr2 ∘ pr2)
      ( tot (λ b → tot (path-pushout-concat-a' a zero-ℕ b)))
      ( b , r , p)
  coherence-path-pushout-a' a (succ-ℕ t) b r p =
    glue-pushout
      ( pr2 ∘ pr2)
      ( tot (λ b → tot (path-pushout-concat-a' a (succ-ℕ t) b)))
      ( b , r , p)

  coherence-path-pushout-b' :
    ( b : B) (t : ℕ) (a : A) (r : R a b) →
    coherence-triangle-maps
      ( inject-path-pushout-b' b t)
      ( path-pushout-concat-a' a (succ-ℕ t) b r)
      ( path-pushout-concat-b' b t a r)
  coherence-path-pushout-b' b zero-ℕ a r p =
    glue-pushout
      ( pr2 ∘ pr2)
      ( tot (λ a → tot (path-pushout-concat-b' b zero-ℕ a)))
      ( a , r , p)
  coherence-path-pushout-b' b (succ-ℕ t) a r p =
    glue-pushout
      ( pr2 ∘ pr2)
      ( tot (λ a → tot (path-pushout-concat-b' b (succ-ℕ t) a)))
      ( a , r , p)

  sequence-first-paths : A → sequential-diagram l
  pr1 (sequence-first-paths a) = path-pushout-type-a' a
  pr2 (sequence-first-paths a) = inject-path-pushout-a' a
```
