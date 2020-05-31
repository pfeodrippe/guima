(ns guima.web-app
  (:require-macros
   [cljs.core.async.macros :refer [go]])
  (:require
   [cljs-http.client :as http]
   [cljs.core.async :refer [<!]]
   [com.fulcrologic.fulcro.application :as app]
   [com.fulcrologic.fulcro.components :as comp :refer [defsc]]
   [com.fulcrologic.fulcro.dom :as d]
   ["codemirror/lib/codemirror" :as CodeMirror]
   ["codemirror/mode/ruby/ruby"]
   ["codemirror/addon/edit/closebrackets"]))

#_(print )
#_(cm)

#_(print (.-cm.CodeMirror js/Comment))

#_(defn- json-parse
    [s]
    (js->clj (js/JSON.parse s) :keywordize-keys true))

#_(defn eval-handler
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
  (when (and parent (.. parent -parentNode))
    (let [cm (CodeMirror. (fn [el]
                            (.. parent -parentNode (replaceChild el parent)))
                          (clj->js {:mode "ruby"
                                    :viewportMargin js/Infinity}))]
      (doto cm
        (.setSize "50%" "auto")
        (.focus)
        (.setOption "autoCloseBrackets" true)))))

(defsc Repl [this {:keys [:cm]}]
  {:initial-state (fn [_] {:cm 0})}
  (d/div {:id "code-and-result",
          :style {:display "flex", :marginTop "20px", :fontSize "20px"}}
    (d/div {:ref add-code-mirror})
    (d/div)))

(def ui-repl (comp/factory Repl))

(defsc Root [this {:keys [:repl]}]
  {:initial-state (fn [_] {:repl (comp/get-initial-state Repl {})})}
  (d/div {}
    (d/div {:style {:display "flex"}}
      (d/div {:style {:display "flex",
                      :justifyContent "flex-start",
                      :width "100%",
                      :padding "10px 15px 7px 10px",
                      :fontSize "14px",
                      :color "#666666"}}
        (d/b "Guima")
        "| A TLA+ REPL")
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
    (ui-repl repl)))

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
