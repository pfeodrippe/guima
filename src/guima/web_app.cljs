(ns guima.web-app
  (:require-macros
   [cljs.core.async.macros :refer [go]])
  (:require
   [cljs-http.client :as http]
   [cljs.core.async :refer [<!]]
   [com.fulcrologic.fulcro.application :as app]
   [com.fulcrologic.fulcro.components :as comp :refer [defsc]]
   [com.fulcrologic.fulcro.dom :as dom]))

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

(defn main!
  []
  (println "OMG"))
