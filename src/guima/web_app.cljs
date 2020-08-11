(ns guima.web-app
  (:require-macros
   [cljs.core.async.macros :refer [go]])
  (:require
   [cemerick.url :as url]
   [clojure.edn :as edn]
   [cljs-http.client :as http]
   [cljs.core.async :refer [<!]]
   [com.fulcrologic.fulcro.application :as app]
   [com.fulcrologic.fulcro.components :as comp :refer [defsc]]
   [com.fulcrologic.fulcro.dom :as d]
   [guima.handler.mutation :as api]
   [com.fulcrologic.fulcro.networking.http-remote :as http-remote]
   [com.fulcrologic.fulcro.algorithms.react-interop :as interop]
   ["codemirror/lib/codemirror" :as CodeMirror]
   ["codemirror/mode/ruby/ruby"]
   ["codemirror/addon/edit/closebrackets"]
   ["draft-js" :refer [Editor, EditorState]]))

(def log js/console.log)

(defonce app (app/fulcro-app
              {:remotes {:remote (http-remote/fulcro-http-remote {})}}))

(def ui-prose-editor (interop/react-factory Editor))

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

(defsc Repl [this
             {:keys [:block.repl/id :block.repl/editor :block.repl/focus
                     :block.repl/result :block.repl/result-error? :block.repl/code]}
             {:keys [:on-create :on-delete]}]
  {:query [:block.repl/id :block.repl/editor :block.repl/focus
           :block.repl/result :block.repl/result-error? :block.repl/code]
   :ident (fn [] [:block.repl/id id])
   :initial-state (fn [{:keys [:block.repl/id :block.repl/code]
                        :or {code ""}}]
                    {:block.repl/id id
                     :block.repl/editor nil
                     :block.repl/focus false
                     :block.repl/result ""
                     :block.repl/result-error? false
                     :block.repl/code code})}
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
                                           {:block.repl/id id
                                            :input code})])

                    (and (.-altKey evt) (= (.-keyCode evt) 13))
                    (on-create id)

                    (and (= (.-keyCode evt) 38)
                         (zero? (.. editor getCursor -line))
                         (zero? (.. editor getCursor -ch)))
                    (comp/transact! this [(api/focus-at-previous-repl
                                           {:block.repl/id id})])

                    (and (= (.-keyCode evt) 40)
                         (= (.. editor lastLine) (.. editor getCursor -line)))
                    (comp/transact! this [(api/focus-at-next-repl
                                           {:block.repl/id id})])

                    :else (comp/transact! this [(api/update-repl-code
                                                 {:block.repl/id id
                                                  :block.repl/code (.getValue editor)})])))
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
                         (comp/transact! this [(api/delete-repl {:block.repl/id id})]))))
                (.on cm "focus"
                     (fn [_cm _evt]
                       (comp/transact! this [(api/focus {:block.repl/id id})])))
                (when code (.setValue cm code))
                (comp/transact! this [(api/add-repl-editor
                                       {:block.repl/id id
                                        :block.repl/editor cm})]))))}
    (d/div :#editor
      {:classes ["w-2/4"]})
    (d/div :.ml-5.text-2xl.self-center
      {:style {:color (if result-error? "#CC0000" "#333333")
               :fontFamily "monospace"}
       :classes ["w-2/4"]}
      result)))

(def ui-repl (comp/computed-factory Repl {:keyfn :block.repl/id}))

(defsc Prose [this
              {:keys [:block.prose/id :block.prose/editor :block.prose/focus :block.prose/result :block.prose/result-error? :block.prose/code :block.prose/text]}
              {:keys [:on-create :on-delete]}]
  {:query [:block.prose/id :block.prose/editor :block.prose/focus :block.prose/result :block.prose/result-error? :block.prose/code :block.prose/text]
   :ident (fn [] [:block.prose/id id])
   :initial-state (fn [{:keys [:block.prose/id :block.prose/code]
                        :or {code ""}}]
                    {:block.prose/id id
                     :block.prose/text ""
                     :block.prose/editor (.createEmpty EditorState)
                     :block.prose/focus nil
                     :block.prose/result ""
                     :block.prose/result-error? false
                     :block.prose/code code})}
  #_(when focus
      (.focus editor))
  (d/div :.flex.text-2xl.p-3
    {:id "code-and-result"}
    (d/div {:style {:fontSize "20px"
                    :fontFamily "georgia,times,serif"}
            :classes ["w-2/4"]}
      (ui-prose-editor {:ref (fn [ref]
                               ref)
                        :editorState editor
                        :handleReturn (fn [a b]
                                        (on-create id)
                                        "handled")
                        :onChange (fn [state]
                                    (comp/transact! this
                                                    [(api/update-prose-editor
                                                      {:block.prose/id id
                                                       :block.prose/editor state})]))}
                       #_{:theme nil
                          :value text
                          :onChange (fn [a b c editor]
                                      (when (= c "user")
                                        (js/console.log text)
                                        (comp/transact! this
                                                        [#_(api/focus {:block.prose/id id})
                                                         (api/update-prose-text
                                                          {:block.prose/id id
                                                           :block.prose/text (.getContents editor)})])))
                          #_ #_:onKeyDown (fn [e]
                                            (when (= (.-keyCode e) 13)
                                              (println 32)
                                              (.preventDefault e)
                                              (on-create id)
                                              false))
                          #_ #_:onFocus (fn []
                                          (println :ID id)
                                          (comp/transact! this [(api/focus {:block.prose/id id})]))
                          #_ #_:onChangeSelection (fn [range]
                                                    (if range
                                                      (do (println :FOCUS id)
                                                          (comp/transact! this [(api/focus {:block.prose/id id})]))
                                                      (do (println :BLUR id)
                                                          (comp/transact! this [(api/blur  {:block.prose/id id})]))))
                          #_ #_:onBlur (fn []
                                         (println :BLUR id)
                                         (comp/transact! this [(api/blur {:block.prose/id id})]))
                          :ref (fn [ref]
                                 #_(log ref)
                                 #_ (when (and ref (nil? focus))
                                      (println :SASx)
                                      (.focus ref))
                                 (when ref
                                   #_(log (.getEditor ref))
                                   (.on (.getEditor ref) "selection-change"
                                        (fn [range old-range source]
                                          (when (= source "user")
                                            (println id range)
                                            (if (some? range)
                                              (.focus ref)
                                              #_(.blur ref)))))))
                          #_ #_:modules {:keyboard {:bindings {:tab true}}}
                          :modules {:keyboard {:bindings #_{:enter {:key 13
                                                                    :empty true
                                                                    :handler (fn [] (on-create id))}}
                                               {:linebreak {:key 13
                                                            :handler (fn [] (on-create id))}}}}}))

    #_(d/div :.ml-5.text-2xl.self-center
        {:style {:color (if result-error? "#CC0000" "#333333")
                 :fontFamily "monospace"}
         :classes ["w-2/4"]}
        result)))

(def ui-prose (comp/computed-factory Prose {:keyfn :repl/id}))

(defsc BlockUnion [this props]
  {:ident (fn []
            (cond
              (:block.repl/id props)  [:block.repl/id (:block.repl/id props)]
              (:block.prose/id props) [:block.prose/id (:block.prose/id props)]
              :else (println :>>>>>>>>>>>>>>>>ERROR!!!)))
   :query (fn [] {:block.repl/id (comp/get-query Repl)
                  :block.prose/id  (comp/get-query Prose)})}
  (cond
    (:block.repl/id props) (ui-repl props)
    (:block.prose/id props) (ui-prose props)
    :else (d/div "Invalid ident used in app state.")))

(def ui-block-union (comp/factory BlockUnion {:keyfn
                                              (fn [props]
                                                (cond
                                                  (:block.repl/id props) [:block.repl/id (:block.repl/id props)]
                                                  (:block.prose/id props) [:block.prose/id (:block.prose/id props)]))}))

(defsc Root [this {:keys [:block/blocks :root/unique-id]}]
  {:query [{:block/blocks {:block.repl/id (comp/get-query #_Prose  Repl)}} :root/unique-id]
   :initial-state (fn [_]
                    (let [b64-state (some-> js/window .-location .-href
                                            url/url :query (get "state"))
                          initial-state (some-> b64-state js/atob edn/read-string)]
                      {:block/blocks (or (some->> (:block/blocks initial-state)
                                                  (map-indexed (fn [idx s]
                                                                 (comp/get-initial-state
                                                                  Prose #_Repl (assoc s :block.repl/id idx))))
                                                  vec)
                                         [(comp/get-initial-state Prose #_Repl {:block.repl/id 0})])
                       :root/unique-id (count (:block/blocks initial-state))}))}
  (d/div
      (d/div :.flex
        (d/div :.justify-start.w-full.py-3.px-3.text-sm
          (d/b "Guima")
          (d/span " | A TLA+ REPL"))
        (d/a :.bg-red-300.hover:bg-red-400.text-gray-800.font-bold.py-2.px-4.rounded.inline-flex.items-center
          {:target "_blank",
           :href "_blank"
           :style {:transform "scale(0.9)"}
           :onClick (fn [e]
                      (.preventDefault e)
                      (let [state {:block/blocks (->> blocks
                                                      (filter :block.repl/editor)
                                                      (mapv #(select-keys % [:block.repl/code])))}
                            clip-url (str (-> js/window .-location .-href
                                              url/url (assoc :query {}))
                                          "?state="
                                          (-> state pr-str js/btoa))]
                        (.. js/navigator -clipboard (writeText clip-url))))}
          (d/span
              "🔗")
          (d/span :.ml-5
            "Share"))
        (d/a :.bg-yellow-300.hover:bg-yellow-400.text-gray-800.font-bold.py-2.px-4.rounded.inline-flex.items-center
          {:target "_blank",
           :href "https://www.buymeacoffee.com/pfeodrippe",
           :style {:transform "scale(0.9)"}}
          (d/img {:src "https://cdn.buymeacoffee.com/buttons/bmc-new-btn-logo.svg"
                  :alt "Buy me a coffee"})
          (d/span :.ml-5
            "Buy me a coffee")))
      (let [on-create (fn [before-id]
                        (comp/transact! this [(api/add-repl {:before-id before-id})]))
            on-delete (fn [id] (comp/transact! this [(api/delete-repl {:block.repl/id id })]))]
        (map #(ui-repl % {:on-create on-create :on-delete on-delete}) blocks)
        #_(map #(ui-prose % {:on-create on-create :on-delete on-delete}) blocks))))

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

(comment

  {0
   {:repl/id 0,
    :repl/editor "UnknownTransitType: [object Object]",
    :repl/focus true,
    :repl/result "",
    :repl/result-error? false,
    :repl/code ""},
   1 {:repl/code "", :repl/focus false}}

  (hash {0
         {:repl/id 0,
          :repl/editor "UnknownTransitType: [object Object]",
          :repl/focus true,
          :repl/result "",
          :repl/result-error? false,
          :repl/code ""},
         1 {:repl/code "", :repl/focus false}})

  (= {0
      {:repl/id 0,
       :repl/editor "UnknownTransitType: [object Object]",
       :repl/focus true,
       :repl/result "",
       :repl/result-error? false,
       :repl/code ""},
      1 {:repl/code "", :repl/focus false}}
     (-> {0
          {:repl/id 0,
           :repl/editor "UnknownTransitType: [object Object]",
           :repl/focus true,
           :repl/result "",
           :repl/result-error? false,
           :repl/code ""},
          1 {:repl/code "", :repl/focus false}}
         js/btoa
         js/atob
         edn/read-string))

  (->> {:block/blocks
        (->> (vals
              {0
               {:repl/id 0,
                :repl/editor "UnknownTransitType: [object Object]",
                :repl/focus true,
                :repl/result "",
                :repl/result-error? false,
                :repl/code "1 + 2"},
               1 {:repl/code "", :repl/focus false}})
             (filter :repl/editor)
             (mapv #(select-keys % [:repl/code])))}
       pr-str
       js/btoa)

  "http://localhost:8080/editor?state=ezpsaXN0L3JlcGxzIFt7OnJlcGwvY29kZSAiMSArIDIifV19"

  ())
