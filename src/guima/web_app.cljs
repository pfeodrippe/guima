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

(defn- json-parse
  [s]
  (js->clj (js/JSON.parse s) :keywordize-keys true))

(defn eval-handler
  [cm]
  (go (let [response (<! (http/post (str (.. js/window -location -origin) "/api/eval-tla-expression")
                                    {:json-params {:input (.getValue cm)}}))
            result-el (.. cm getWrapperElement -parentNode (querySelector "#result"))
            body (json-parse (:body response))]
        (if (= (:status response) 200)
          (do (set! (.-color (.-style result-el)) "#333333")
              (set! (.-innerHTML result-el) (:data body)))
          (do (set! (.-color (.-style result-el)) "#cc0000")
              (set! (.-innerHTML result-el)
                    (get-in body [:error :message])))))))

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
                                  :viewportMargin js/Infinity
                                  #_ #_:extraKeys {"Shift-Enter" eval-handler
                                                   "Ctrl-Enter" eval-handler}}))]
    (doto cm
      (.setSize "50%" "auto")
      #_(.focus)
      (.setOption "autoCloseBrackets" true))))

;; Creates a new Repl component.
;; `0` is the initial id.
(defsc Repl [this {:keys [:repl/id :repl/editor :repl/focus]} {:keys [:on-create :on-delete]}]
  {:query [:repl/id :repl/editor :repl/focus]
   :ident (fn [] [:repl/id id])
   :initial-state (fn [{:keys [:repl/id]}]
                    {:repl/id id :repl/editor nil :repl/focus false})}
  (when focus
    (.focus editor))
  (d/div {:id "code-and-result",
          :onKeyDown (fn [evt]
                       ;; keycode 13 - Enter
                       ;; keycode 38 - ArrowUp
                       ;; keycode 40 - ArrowDown
                       (log (.-keyCode evt))
                       (cond
                         (or (and (.-ctrlKey evt)  (= (.-keyCode evt) 13))
                             (and (.-shiftKey evt) (= (.-keyCode evt) 13)))
                         (comp/transact! this [(api/eval-tla-expression {:a 2})])

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
          :style {:display "flex", :marginTop "20px", :fontSize "20px"}
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
                     (comp/transact! this [(api/add-repl-editor
                                            {:repl/id id
                                             :repl/editor cm})]))))}
    (d/div :#editor)
    (d/div {:id "result",
            :style {:marginLeft "10px",
                    :fontSize "100%",
                    :alignSelf "center",
                    :fontFamily "monospace",
                    :width "50%"}})))

(def ui-repl (comp/computed-factory Repl {:keyfn :repl/id }))

(defsc Root [this {:keys [:list/repls :root/unique-id]}]
  {:query [{:list/repls (comp/get-query Repl)} :root/unique-id]
   :initial-state (fn [_] {:list/repls [(comp/get-initial-state Repl {:repl/id 0})]
                           :root/unique-id 0})}
  (d/div {}
    (d/div {:style {:display "flex"}}
      (d/div {:style {:display "flex",
                      :justifyContent "flex-start",
                      :width "100%",
                      :padding "10px 15px 7px 10px",
                      :fontSize "14px",
                      :color "#666666"}}
        (d/b "Guima")
        (d/span "| A TLA+ REPL"))
      (d/div {:style {:display "flex",
                      :justifyContent "flex-end",
                      :width "100%",
                      :padding "0"}}
        (d/a :.bmc-button
          {:target "_blank",
           :href "https://www.buymeacoffee.com/pfeodrippe",
           :style {:transform "scale(0.5)"}}
          (d/img {:src "https://cdn.buymeacoffee.com/buttons/bmc-new-btn-logo.svg"
                  :alt "Buy me a coffee"})
          (d/span {:style {:marginLeft "5px", :fontSize "19px !important"}}
            "Buy me a coffee"))))
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
