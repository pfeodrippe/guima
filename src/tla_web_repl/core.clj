(ns tla-web-repl.core
  (:require
   [clojure.java.shell :as sh]
   [jsonista.core :as json]
   [pohjavirta.server :as server]))

(comment

  (time
   (->> (doall (map (fn [_]
                       (sh/with-sh-env {"PLUSPYPATH"
                                        ".:./PlusPy/modules/lib:./PlusPy/modules/book:./PlusPy/modules/other"}
                         (sh/sh "python3" "PlusPy/pluspy.py" "-c2" "HourClock")))
                    (range 40)))
        (map :out)
        (map println)))

  (time
   (->> (doall (pmap (fn [_]
                       (sh/with-sh-env {"PLUSPYPATH"
                                        ".:./PlusPy/modules/lib:./PlusPy/modules/book:./PlusPy/modules/other"}
                         (sh/sh "python3" "PlusPy/pluspy.py" "-c2" "HourClock")))
                     (range 40)))
        (map :out)
        (map println)))

  ())

(defn handler [_]
  {:status 200
   :headers {"Content-Type" "application/json"}
   :body (json/write-value-as-bytes {:message "hello"})})

;; create and start the server
#_(-> #'handler server/create server/start)
