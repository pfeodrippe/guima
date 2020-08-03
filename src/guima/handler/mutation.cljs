(ns guima.handler.mutation
  (:require
   [com.fulcrologic.fulcro.components :as comp :refer [defsc]]
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
          nil (:block/blocks s)))

(defn- get-next-id
  [s id]
  (reduce (fn [next-id [ident old-id]]
            (if (= old-id id)
              (reduced next-id)
              old-id))
          nil (reverse (:block/blocks s))))

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
                                          [] (:block/blocks s))]
                     (-> s
                         (assoc-in [:repl/id id] {:repl/id id})
                         (assoc :block/blocks new-list)
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
                        (merge/remove-ident* [:repl/id id] [:block/blocks]))))))

(defmutation focus-at-previous-repl
  [{:keys [:repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [previous-id (get-previous-id % id)]
                    (if previous-id
                      (-> %
                          remove-all-focus
                          (update-in [:repl/id previous-id] assoc :repl/focus true))
                      %)))))

(defmutation focus
  [{:keys [:repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(-> %
                      remove-all-focus
                      (update-in [:repl/id id] assoc :repl/focus true)))))

(defmutation focus-at-next-repl
  [{:keys [:repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [next-id (get-next-id % id)]
                    (if next-id
                      (-> %
                          remove-all-focus
                          (update-in [:repl/id next-id] assoc :repl/focus true))
                      %)))))

(defmutation update-repl-code
  [{:keys [:repl/id :repl/code]}]
  (action [{:keys [:state]}]
    (swap! state update-in [:repl/id id] assoc
           :repl/code code)))

(defmutation update-repl-result
  [{:keys [:repl/id :repl/result :repl/result-error?]}]
  (action [{:keys [:state]}]
    (swap! state update-in [:repl/id id] assoc
           :repl/result result
           :repl/result-error? result-error?)))

(defmutation eval-tla-expression
  [{:keys [:repl/id]}]
  (ok-action [{:keys [:app :result]}]
    (let [body (get-in result [:body `eval-tla-expression])]
      (if (:error body)
        (comp/transact! app [(update-repl-result {:repl/id id
                                                  :repl/result (get-in body [:error :message])
                                                  :repl/result-error? true})])
        (comp/transact! app [(update-repl-result {:repl/id id
                                                  :repl/result (:data body)
                                                  :repl/result-error? false})]))))
  (remote [env] true))
