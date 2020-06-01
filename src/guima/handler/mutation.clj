(ns guima.handler.mutation
  (:require
   [com.wsscode.pathom.connect :as pc]))

(pc/defmutation eval-tla-expression [env {:keys [:input]}]
  {::pc/sym `eval-tla-expression}
  "ABC")

(def mutations [eval-tla-expression])
