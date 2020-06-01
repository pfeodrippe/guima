(ns guima.web-app.mutation
  (:require
   [com.fulcrologic.fulcro.mutations :as m :refer [defmutation]]
   [com.fulcrologic.fulcro.algorithms.merge :as merge]))

(defn- remove-all-focus
  [s]
  (update s :repl/id (fn [id->repl]
                       (->> (map (fn [[id repl]]
                                   [id (assoc repl :repl/focus false)])
                                 id->repl)
                            (into {})))))

(defmutation add-repl
  [{:keys [:repl/id :before-id]}]
  (action [{:keys [:state]}]
    (swap! state (fn [s]
                   ;; find index position using `before-id` and put new repl after it
                   (let [new-list (reduce (fn [acc [ident old-id]]
                                            (if (= old-id before-id)
                                              (conj acc [ident old-id] [:repl/id id])
                                              (conj acc [ident old-id])))
                                          [] (:list/repls s))]
                     (-> s
                         (assoc-in [:repl/id id] {:repl/id id})
                         (assoc :list/repls new-list :root/unique-id (inc id))))))))

(defmutation add-repl-editor
  [{:keys [:repl/id :repl/editor]}]
  (action [{:keys [:state]}]
    (swap! state #(-> %
                      remove-all-focus
                      (update-in [:repl/id id] assoc :repl/editor editor :repl/focus true)))))

(defmutation delete-repl
  [{:keys [:repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [anterior-id (reduce (fn [anterior-id [ident old-id]]
                                              (if (= old-id id)
                                                (reduced anterior-id)
                                                old-id))
                                            nil (:list/repls %))]
                    (-> %
                        remove-all-focus
                        (update :repl/id dissoc id)
                        (update-in [:repl/id anterior-id] assoc :repl/focus true)
                        (merge/remove-ident* [:repl/id id] [:list/repls]))))))
