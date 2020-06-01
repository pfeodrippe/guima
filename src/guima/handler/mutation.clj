(ns guima.handler.mutation
  (:require
   [com.wsscode.pathom.connect :as pc]
   [guima.server.tla :as tla]))

(pc/defmutation eval-tla-expression [env {:keys [:input]}]
  {::pc/sym `eval-tla-expression}
  (println :INP input)
  (tla/eval-tla-expression input))

(def mutations [eval-tla-expression])
