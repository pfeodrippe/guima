(ns guima.web-app
  (:require-macros
   [cljs.core.async.macros :refer [go]])
  (:require
   [cljs-http.client :as http]
   [cljs.core.async :refer [<!]]
   [com.fulcrologic.fulcro.application :as app]
   [com.fulcrologic.fulcro.components :as comp :refer [defsc]]
   [com.fulcrologic.fulcro.dom :as d]
   [guima.handler.mutation :as api]
   [com.fulcrologic.fulcro.networking.http-remote :as http-remote]
   ["codemirror/lib/codemirror" :as CodeMirror]
   ["codemirror/mode/ruby/ruby"]
   ["codemirror/addon/edit/closebrackets"]))

(def log js/console.log)

(defonce app (app/fulcro-app
              {:remotes {:remote (http-remote/fulcro-http-remote {})}}))

(defn add-code-mirror
  [parent]
  (let [editor-div (.querySelector parent "#editor")
        result-div (.querySelector parent "#result")
        cm (CodeMirror. (fn [el]
                          (.. parent (replaceChild el editor-div)))
                        (clj->js {:mode "ruby"
                                  :viewportMargin js/Infinity}))]
    (doto cm
      (.setSize "50%" "auto")
      (.setOption "autoCloseBrackets" true))))

;; Creates a new Repl component.
;; `0` is the initial id.
(defsc Repl [this
             {:keys [:repl/id :repl/editor :repl/focus :repl/result :repl/result-error?]}
             {:keys [:on-create :on-delete]}]
  {:query [:repl/id :repl/editor :repl/focus :repl/result :repl/result-error?]
   :ident (fn [] [:repl/id id])
   :initial-state (fn [{:keys [:repl/id]}]
                    {:repl/id id
                     :repl/editor nil
                     :repl/focus false
                     :repl/result ""
                     :repl/result-error? false})}
  (when focus
    (.focus editor))
  (d/div :.flex.mt-10.text-2xl
    {:id "code-and-result",
     :onKeyDown (fn [evt]
                  ;; keycode 13 - Enter
                  ;; keycode 38 - ArrowUp
                  ;; keycode 40 - ArrowDown
                  (cond
                    (or (and (.-ctrlKey evt)  (= (.-keyCode evt) 13))
                        (and (.-shiftKey evt) (= (.-keyCode evt) 13)))
                    (comp/transact! this [(api/eval-tla-expression
                                           {:repl/id id
                                            :input (.getValue editor)})])

                    (and (.-altKey evt) (= (.-keyCode evt) 13))
                    (on-create id)

                    (and (= (.-keyCode evt) 38)
                         (zero? (.. editor getCursor -line))
                         (zero? (.. editor getCursor -ch)))
                    (comp/transact! this [(api/focus-at-previous-repl
                                           {:repl/id id})])

                    (and (= (.-keyCode evt) 40)
                         (= (.. editor lastLine) (.. editor getCursor -line)))
                    (comp/transact! this [(api/focus-at-next-repl
                                           {:repl/id id})])

                    :else evt))
     :ref (fn [ref]
            (when (and ref (.querySelector ref "#editor"))
              (let [cm (add-code-mirror ref)]
                (.on cm "beforeChange"
                     (fn [cm evt]
                       (when (and (not (zero? id))
                                  (empty? (.getValue cm))
                                  (zero? (.. evt -to -line))
                                  (zero? (.. evt -to -ch))
                                  (= (.. evt -origin) "+delete"))
                         (comp/transact! this [(api/delete-repl {:repl/id id})]))))
                (.on cm "focus"
                     (fn [_cm _evt]
                       (comp/transact! this [(api/focus {:repl/id id})])))
                (comp/transact! this [(api/add-repl-editor
                                       {:repl/id id
                                        :repl/editor cm})]))))}
    (d/div :#editor
      {:classes ["w-2/4"]})
    (d/div :.ml-5.text-2xl.self-center
      {:style {:color (if result-error? "#CC0000" "#333333")
               :fontFamily "monospace"}
       :classes ["w-2/4"]}
      result)))

(def ui-repl (comp/computed-factory Repl {:keyfn :repl/id }))

(defsc Root [this {:keys [:list/repls :root/unique-id]}]
  {:query [{:list/repls (comp/get-query Repl)} :root/unique-id]
   :initial-state (fn [_] {:list/repls [(comp/get-initial-state Repl {:repl/id 0})]
                           :root/unique-id 0})}
  (d/div
    (d/div :.flex
      (d/div :.justify-start.w-full.py-3.px-3.text-sm
        (d/b "Guima")
        (d/span " | A TLA+ REPL"))
      (d/a :.bg-yellow-300.hover:bg-yellow-400.text-gray-800.font-bold.py-2.px-4.rounded.inline-flex.items-center
        {:target "_blank",
         :href "https://www.buymeacoffee.com/pfeodrippe",
         :style {:transform "scale(0.7)"}}
        (d/img {:src "https://cdn.buymeacoffee.com/buttons/bmc-new-btn-logo.svg"
                :alt "Buy me a coffee"})
        (d/span :.ml-5
          "Buy me a coffee")))
    (let [on-create (fn [before-id]
                      (comp/transact! this [(api/add-repl {:before-id before-id})]))
          on-delete (fn [id] (comp/transact! this [(api/delete-repl {:repl/id id })]))]
      (map #(ui-repl % {:on-create on-create :on-delete on-delete}) repls))))

(defn ^:export refresh
  "During development, shadow-cljs will call this on every hot reload of source. See shadow-cljs.edn"
  []
  ;; re-mounting will cause forced UI refresh, update internals, etc.
  (app/mount! app Root "app")
  (js/console.log "Hot reload"))

(defn ^:export main!
  []
  (app/mount! app Root "app")
  (js/console.log "Loaded"))
