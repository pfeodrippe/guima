(ns guima.web-app.mutation
  (:require
   [com.fulcrologic.fulcro.mutations :as m :refer [defmutation]]
   [com.fulcrologic.fulcro.algorithms.merge :as merge]))

(defmutation add-repl
  [{:keys [:repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(-> %
                      (assoc-in [:repl/id id] {:repl/id id})
                      (assoc-in [:list/repls id] [:repl/id id])))))
