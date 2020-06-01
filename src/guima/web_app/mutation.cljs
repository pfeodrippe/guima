(ns guima.web-app.mutation
  (:require
   [com.fulcrologic.fulcro.mutations :as m :refer [defmutation]]
   [com.fulcrologic.fulcro.algorithms.merge :as merge]))

(defmutation add-repl
  [{:keys [:repl/id :before-id]}]
  (action [{:keys [:state]}]
    (swap! state (fn [s]
                   ;; find index position using `before-id`
                   (let [new-list (reduce (fn [acc [ident old-id]]
                                            (if (= old-id before-id)
                                              (conj acc [ident old-id] [:repl/id id])
                                              (conj acc [ident old-id])))
                                          [] (:list/repls s))]
                     (-> s
                         (assoc-in [:repl/id id] {:repl/id id})
                         (assoc :list/repls new-list)))))))
