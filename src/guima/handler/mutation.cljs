(ns guima.handler.mutation
  (:require
   [com.fulcrologic.fulcro.components :as comp :refer [defsc]]
   [com.fulcrologic.fulcro.mutations :as m :refer [defmutation]]
   [com.fulcrologic.fulcro.algorithms.merge :as merge]))

(defn- remove-all-focus
  [s]
  (update s :block.repl/id (fn [id->repl]
                       (->> (map (fn [[id repl]]
                                   [id (assoc repl :block.repl/focus false)])
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
                                              (conj acc [ident old-id] [:block.repl/id id])
                                              (conj acc [ident old-id])))
                                          [] (:block/blocks s))]
                     (-> s
                         (assoc-in [:block.repl/id id] {:block.repl/id id
                                                        :block.repl/editor nil
                                                        :block.repl/focus false
                                                        :block.repl/result ""
                                                        :block.repl/result-error? false
                                                        :block.repl/code ""})
                         (assoc :block/blocks new-list)
                         (assoc :root/unique-id id)))))))

(defmutation add-prose-block
  [{:keys [:before-id]}]
  (action [{:keys [:state]}]
    (swap! state (fn [s]
                   ;; find index position using `before-id` and put new repl after it
                   (let [id (inc (:root/unique-id s))
                         new-list (reduce (fn [acc [ident old-id]]
                                            (if (= old-id before-id)
                                              (conj acc [ident old-id] [:block.prose/id id])
                                              (conj acc [ident old-id])))
                                          [] (:block/blocks s))]
                     (-> s
                         (assoc-in [:block.prose/id id] {:block.prose/id id
                                                        :block.prose/editor nil
                                                        :block.prose/focus false
                                                        :block.prose/result ""
                                                        :block.prose/result-error? false
                                                        :block.prose/code ""})
                         (assoc :block/blocks new-list)
                         (assoc :root/unique-id id)))))))

(defmutation add-repl-editor
  [{:keys [:block.repl/id :block.repl/editor]}]
  (action [{:keys [:state]}]
    (swap! state #(-> %
                      remove-all-focus
                      (update-in [:block.repl/id id] assoc :block.repl/editor editor :block.repl/focus true)))))

(defmutation delete-repl
  [{:keys [:block.repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [previous-id (get-previous-id % id)]
                    (-> %
                        remove-all-focus
                        (update :block.repl/id dissoc id)
                        #_(update-in [:block.repl/id previous-id] assoc :block.repl/focus true)
                        (merge/remove-ident* [:block.repl/id id] [:block/blocks]))))))

(defmutation focus-at-previous-repl
  [{:keys [:block.repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [previous-id (get-previous-id % id)]
                    (if previous-id
                      (-> %
                          remove-all-focus
                          (update-in [:block.repl/id previous-id] assoc :block.repl/focus true))
                      %)))))

(defmutation focus
  [{:keys [:block.repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(-> %
                      remove-all-focus
                      (update-in [:block.repl/id id] assoc :block.repl/focus true)))))

(defmutation blur
  [{:keys [:block.repl/id]}]
  (action [{:keys [:state]}]
    (swap! state update-in [:block.repl/id id] assoc :block.repl/focus false)))

(defmutation focus-at-next-repl
  [{:keys [:block.repl/id]}]
  (action [{:keys [:state]}]
    (swap! state #(let [next-id (get-next-id % id)]
                    (if next-id
                      (-> %
                          remove-all-focus
                          (update-in [:block.repl/id next-id] assoc :block.repl/focus true))
                      %)))))

(defmutation update-repl-code
  [{:keys [:block.repl/id :block.repl/code]}]
  (action [{:keys [:state]}]
    (swap! state update-in [:block.repl/id id] assoc
           :block.repl/code code)))

(defmutation update-prose-text
  [{:keys [:block.prose/id :block.prose/text]}]
  (action [{:keys [:state]}]
    (swap! state update-in [:block.prose/id id] assoc
           :block.prose/text text)))

(defmutation update-prose-editor
  [{:keys [:block.prose/id :block.prose/editor]}]
  (action [{:keys [:state]}]
    (swap! state update-in [:block.prose/id id] assoc
           :block.prose/editor editor)))

(defmutation update-repl-result
  [{:keys [:block.repl/id :block.repl/result :block.repl/result-error?]}]
  (action [{:keys [:state]}]
    (swap! state update-in [:block.repl/id id] assoc
           :block.repl/result result
           :block.repl/result-error? result-error?)))

(defmutation eval-tla-expression
  [{:keys [:block.repl/id]}]
  (ok-action [{:keys [:app :result]}]
    (let [body (get-in result [:body `eval-tla-expression])]
      (if (:error body)
        (comp/transact! app [(update-repl-result {:block.repl/id id
                                                  :block.repl/result (get-in body [:error :message])
                                                  :block.repl/result-error? true})])
        (comp/transact! app [(update-repl-result {:block.repl/id id
                                                  :block.repl/result (:data body)
                                                  :block.repl/result-error? false})]))))
  (remote [env] true))
