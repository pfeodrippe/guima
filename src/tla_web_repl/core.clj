(ns tla-web-repl.core
  (:require
   [clojure.java.shell :as sh]
   [jsonista.core :as json]
   [pohjavirta.server :as server]
   [clojure.string :as str]))

;; From http://makble.com/clojure-regular-expression-extract-text-between-two-strings
(defn make-literal [a]
  (.replace a "\"" "\\\""))

(defn- extract-anything-between [prefix suffix from-string]
  (let [pattern (str (make-literal prefix) "([\\s\\S]*?)" (make-literal suffix))]
    (second (re-find (re-pattern pattern) from-string))))

(def ^:private spec-template
  "
----------------------------- MODULE %s -----------------------------
EXTENDS Naturals, Sequences, IOUtils, FiniteSets, TLC
%s
Init == /\\ IOPut(\"fd\", \"stdout\", \"\\nTLAREPL_START\\n\")
        /\\ IOPut(\"fd\", \"stdout\", %s)
        /\\ IOPut(\"fd\", \"stdout\", \"\\nTLAREPL_END\\n\")
        /\\ TRUE

Next == TRUE
Spec == Init
=================================================================================
")

(defn- run-repl
  [spec]
  (sh/with-sh-env {"PLUSPYPATH"
                   ".:./PlusPy/modules/lib:./PlusPy/modules/book:./PlusPy/modules/other:/tmp"}
    (sh/sh "python3" "PlusPy/pluspy.py" "-c2" spec)))

(defn- eval-tla
  [ctx expr]
  (let [{:keys [:out :exit] :as response}
        (let [spec-file (java.io.File/createTempFile "TLAWebREPL" ".tla")
              spec-name (-> (.getName spec-file) (str/split #"\.") first)]
          (println (.getAbsolutePath spec-file))
          (spit spec-file (format spec-template spec-name ctx expr))
          (run-repl spec-name))]
    (if-not (zero? exit)
      response
      (try
        (if (re-find #"TLAREPL_START" out)
          (->> out
               (extract-anything-between "TLAREPL_START" "TLAREPL_END")
               (#(subs % 1 (dec (count %)))))
          (do (print out)
              out))
        (catch Exception _
          (print out))))))

(comment

  ;; Working section -------------------
  (eval-tla "" "3 + 5")

  (eval-tla "" "<<4, 5, 5>> \\o <<10>>")

  (eval-tla "" "60 \\div 7")

  (eval-tla (->> [
                  "IndexOf(seq, elem) == CHOOSE i \\in 1..Len(seq): seq[i] = elem"]
                 (str/join "\n"))
            "IndexOf(<<3, 6, 7>>, 3)")

  (eval-tla "" "1 \\in {3, 4, 1}")

  (eval-tla "" "Len(<<3, 2>>)")

  (eval-tla "" "Head(<<3, 2>>)")

  (eval-tla "" "Tail(<<4, 12>>)")

  (eval-tla "" "{1, 2} \\subseteq {1, 2, 3}")

  (eval-tla "" "Cardinality({3})")

  (eval-tla "" "{2, 3} \\cup {50, 2}")

  ())

(comment

  (sh/with-sh-env {"PLUSPYPATH"
                   ".:/tmp:./PlusPy/modules/lib:./PlusPy/modules/book:./PlusPy/modules/other"}
    (sh/sh "python3" "PlusPy/pluspy.py" "-c2" "TLAWebREPL4042280218357438252.tla"))

  (sh/with-sh-env {"PLUSPYPATH"
                   ".:/tmp:./PlusPy/modules/lib:./PlusPy/modules/book:./PlusPy/modules/other"}
    (sh/sh "python3" "PlusPy/pluspy.py" "-c2" "TLAWebREPL9349548938100035477.tla"))

  (time
   (->> (doall (map (fn [_]
                      (sh/with-sh-env {"PLUSPYPATH"
                                       ".:/tmp:./PlusPy/modules/lib:./PlusPy/modules/book:./PlusPy/modules/other"}
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
