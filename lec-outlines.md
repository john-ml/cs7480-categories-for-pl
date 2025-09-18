# Lecture 5: Internal languages, exponential

1. Interpreting calc in a cateogry with finite products
    * Recall the interpretations of types and terms 
    * Theorem: Every category with finite products is a model of calc, meaning:
        * Contexts and types are objects
        * Terms are morphisms
        * Equational theory is validated
    * Equational theory is not contextual equivalence: this is not compiler correctness 
      or full abstraction. The category is not a *target language*, it is a *model*
    * Why do we do this?
        * If language is object of interest, then this gives us models of language which can 
          prove metatheorems (i.e., consistency).
        * If category is object of interest, then it gives us a concise way of describing 
            properties of the category. This is equations that are true in the "source language"
            must be true in the category.
2. Give an example of establishing commutativity of products:
    * Small calc language extended with two new types X and Y, the beta and eta laws 
      prove the necessary equalities of morphisms!
3. 