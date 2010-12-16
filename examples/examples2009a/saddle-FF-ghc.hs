import Common

run = let start = [1, 1]
          f x1 y1 x2 y2 = ((sqr x1) + (sqr y1)) - ((sqr x2) + (sqr y2))
          [x1_star, y1_star] =
              multivariate_argmin
              (\ [x1, y1] ->
                   multivariate_max
                   (\ [x2, y2] -> f (lift x1) (lift y1) x2 y2)
                   (map lift start))
              start
          [x2_star, y2_star] =
              multivariate_argmax
              (\ [x2, y2] -> f (lift x1_star) (lift y1_star) x2 y2)
              start
       in [[x1_star, y1_star], [x2_star, y2_star]]

main = print run
