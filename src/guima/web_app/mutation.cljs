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

(defn- get-previous-id
  [s id]
  (reduce (fn [previous-id [ident old-id]]
            (if (= old-id id)
              (reduced previous-id)
              old-id))
          nil (:list/repls s)))

(defn- get-next-id
  [s id]
  (reduce (fn [next-id [ident old-id]]
            (if (= old-id id)
              (reduced next-id)
              old-id))
          nil (reverse (:list/repls s))))

(defmutation add-repl
  [{:keys [:before-id]}]
  (action [{:keys [:state]}]
    (swap! state (fn [s]
                   ;; find index position using `before-id` and put new repl after it
                   (let [id (inc (:root/unique-id s))
                         new-list (reduce (fn [acc [ident old-id]]
                                            (if (= old-id before-id)
                                              (conj acc [ident old-id] [:repl/id id])
                                              (conj acc [ident old-id])))
                                          [] (:list/repls s))]
                     (-> s
                         (assoc-in [:repl/id id] {:repl/id id})
                         (assoc :list/repls new-list)
                         (assoc :root/unique-id id)))))))

(defmutation add-repl-editor
  [{:keys [:repl/id :repl/editor]}]
  (action [{:keys [:state]}]
    (swap! state #(-> %
                      remove-all-focus
                      (update-in [:repl/id id] assoc :repl/editor editor :repl/focus true)))))

(defmutation delete-repl
  [{:keys [:repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [previous-id (get-previous-id % id)]
                    (-> %
                        remove-all-focus
                        (update :repl/id dissoc id)
                        (update-in [:repl/id previous-id] assoc :repl/focus true)
                        (merge/remove-ident* [:repl/id id] [:list/repls]))))))

(defmutation focus-at-previous-repl
  [{:keys [:repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [previous-id (get-previous-id % id)]
                    (if previous-id
                      (-> %
                          remove-all-focus
                          (update-in [:repl/id previous-id] assoc :repl/focus true))
                      %)))))

(defmutation focus-at-next-repl
  [{:keys [:repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [next-id (get-next-id % id)]
                    (if next-id
                      (-> %
                          remove-all-focus
                          (update-in [:repl/id next-id] assoc :repl/focus true))
                      %)))))
