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
   ["codemirror/mode/ruby/ruby"]))

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

(defn code-mirror
  [parent]
  (CodeMirror. (.getElementById js/document "app")
               (clj->js {:mode "ruby"
                         :viewportMargin js/Infinity})))

(defsc Repl [this {:keys [:cm]}]
  {:initial-state (fn [_] {:cm (code-mirror 0)})}
  (d/div (CodeMirror. (.getElementById js/document "app")
                      (clj->js {:mode "ruby"
                                :viewportMargin js/Infinity}))))

(def ui-repl (comp/factory Repl))

(defsc Root [this {:keys [:repl]}]
  {:initial-state (fn [_] {:repl (comp/get-initial-state Repl {})})}
  (d/div (ui-repl repl)))

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
