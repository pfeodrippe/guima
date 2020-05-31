(ns guima.web-app
  (:require-macros
   [cljs.core.async.macros :refer [go]])
  (:require
   [cljs-http.client :as http]
   [cljs.core.async :refer [<!]]
   [com.fulcrologic.fulcro.application :as app]
   [com.fulcrologic.fulcro.components :as comp :refer [defsc]]
   [com.fulcrologic.fulcro.dom :as d]
   [guima.web-app.mutation :as api]
   ["codemirror/lib/codemirror" :as CodeMirror]
   ["codemirror/mode/ruby/ruby"]
   ["codemirror/addon/edit/closebrackets"]))

#_(print )
#_(cm)

#_(print (.-cm.CodeMirror js/Comment))

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

(defonce app (app/fulcro-app))

(defn add-code-mirror
  [parent]
  (when (and parent (.querySelector parent "#editor"))
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
        (.focus)
        (.setOption "autoCloseBrackets" true)))))

(defsc Repl [this {:keys [:repl/id]} {:keys [:on-create]}]
  {:query [:repl/id]
   :ident (fn [] [:repl/id id])
   :initial-state (fn [{:keys [:repl/id]}] {:repl/id id})}
  (d/div {:id "code-and-result",
          :onKeyDown (fn [evt]
                       (log evt)
                       (cond
                         (and (.-ctrlKey evt) (= (.-keyCode evt) 13))
                         (do (log "OLA") (.preventDefault evt))

                         (and (.-altKey evt) (= (.-keyCode evt) 13))
                         (on-create id)

                         :else evt))
          :style {:display "flex", :marginTop "20px", :fontSize "20px"}
          :ref add-code-mirror}
    (d/div :#editor)
    (d/div {:id "result",
            :style {:marginLeft "10px",
                    :fontSize "100%",
                    :alignSelf "center",
                    :fontFamily "monospace",
                    :width "50%"}})))

(def ui-repl (comp/computed-factory Repl {:keyfn :repl/id }))

(defsc Root [this {:keys [:list/repls]}]
  {:query [{:list/repls (comp/get-query Repl)}]
   :initial-state (fn [_] {:list/repls [(comp/get-initial-state Repl {:repl/id 0})]})}
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
                      (comp/transact! this [(api/add-repl {:repl/id (count repls)
                                                           :before-id before-id})]))]
      (map #(ui-repl % {:on-create on-create}) repls))))

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
