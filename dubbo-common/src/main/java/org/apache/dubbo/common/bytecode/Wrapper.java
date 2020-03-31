/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.dubbo.common.bytecode;

import org.apache.dubbo.common.utils.ClassUtils;
import org.apache.dubbo.common.utils.ReflectUtils;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;

/**
 * Wrapper.
 */
public abstract class Wrapper {
    private static final Map<Class<?>, Wrapper> WRAPPER_MAP = new ConcurrentHashMap<Class<?>, Wrapper>(); //class wrapper map
    private static final String[] EMPTY_STRING_ARRAY = new String[0];
    private static final String[] OBJECT_METHODS = new String[]{"getClass", "hashCode", "toString", "equals"};
    private static final Wrapper OBJECT_WRAPPER = new Wrapper() {
        @Override
        public String[] getMethodNames() {
            return OBJECT_METHODS;
        }

        @Override
        public String[] getDeclaredMethodNames() {
            return OBJECT_METHODS;
        }

        @Override
        public String[] getPropertyNames() {
            return EMPTY_STRING_ARRAY;
        }

        @Override
        public Class<?> getPropertyType(String pn) {
            return null;
        }

        @Override
        public Object getPropertyValue(Object instance, String pn) throws NoSuchPropertyException {
            throw new NoSuchPropertyException("Property [" + pn + "] not found.");
        }

        @Override
        public void setPropertyValue(Object instance, String pn, Object pv) throws NoSuchPropertyException {
            throw new NoSuchPropertyException("Property [" + pn + "] not found.");
        }

        @Override
        public boolean hasProperty(String name) {
            return false;
        }

        @Override
        public Object invokeMethod(Object instance, String mn, Class<?>[] types, Object[] args) throws NoSuchMethodException {
            if ("getClass".equals(mn)) {
                return instance.getClass();
            }
            if ("hashCode".equals(mn)) {
                return instance.hashCode();
            }
            if ("toString".equals(mn)) {
                return instance.toString();
            }
            if ("equals".equals(mn)) {
                if (args.length == 1) {
                    return instance.equals(args[0]);
                }
                throw new IllegalArgumentException("Invoke method [" + mn + "] argument number error.");
            }
            throw new NoSuchMethodException("Method [" + mn + "] not found.");
        }
    };
    private static AtomicLong WRAPPER_CLASS_COUNTER = new AtomicLong(0);

    private static final String CODE_SET_PROPERTY_METHOD_PREFIX = "public void setPropertyValue(Object o, String n, Object v){ ";

    private static final String CODE_GET_PROPERTY_METHOD_PREFIX = "public Object getPropertyValue(Object o, String n){ ";

    private static final String CODE_INVOKE_METHOD_PREFIX = "public Object invokeMethod(Object o, String n, Class[] p, Object[] v) throws java.lang.reflect.InvocationTargetException { ";

    private static final String CODE_GET_TARGET_OBJECT = "%s w; try{ w = ((%s)$1); } catch(Throwable e) { throw new IllegalArgumentException(e); }";

    private static final String CODE_GETTER = " if( $2.equals(\"%s\") ) { return ($w)w.%s(); } ";

    private static final String CODE_SETTER = " if( $2.equals(\"%s\") ){ w.%s(%s); return; }";

    private static final String CODE_SET_FIELD = " if( $2.equals(\"%s\") ) { w.%s=%s; return; }";

    private static final String CODE_GET_FIELD = " if( $2.equals(\"%s\") ) { return ($w)w.%s; }";

    private static final String CODE_THROW_NO_SUCH_METHOD = " throw new org.apache.dubbo.common.bytecode.NoSuchMethodException(\"Not found property \\\"\"+$2+\"\\\" field or setter method in class %s.\"); }";

    private static final String CODE_TRY_METHOD_PREFIX = " try {";

    private static final String CODE_TRY_METHOD_SUFFIX = " } catch(Throwable e) { throw new java.lang.reflect.InvocationTargetException(e); } ";

    private static final String CODE_CHECK_PARAM = " if ( \"%s\".equals( $2 )  &&  $3.length == %d ";

    private static final String CODE_CHECK_OVERRIDE = " && $3[%d].getName().equals(\"%s\")";

    private static final String CODE_END_CHECK = " ) ";

    private static final String CODE_INVOKE_VOID_RETURN = "{ w.%s(%s); return null; }";

    private static final String CODE_INVOKE_OBJECT_RETURN = "{ return ($w)w.%s(%s); }";

    /**
     * get wrapper.
     *
     * @param c Class instance.
     * @return Wrapper instance(not null).
     */
    public static Wrapper getWrapper(Class<?> c) {
        while (ClassGenerator.isDynamicClass(c)) // can not wrapper on dynamic class.
        {
            c = c.getSuperclass();
        }

        if (c == Object.class) {
            return OBJECT_WRAPPER;
        }

        return WRAPPER_MAP.computeIfAbsent(c, Wrapper::makeWrapper);
    }

    private static Wrapper makeWrapper(Class<?> c) {
        if (c.isPrimitive()) {
            throw new IllegalArgumentException("Can not create wrapper for primitive type: " + c);
        }

        String clazzName = c.getName();
        ClassLoader classLoader = ClassUtils.getClassLoader(c);

        StringBuilder setPropertyCode = new StringBuilder(CODE_SET_PROPERTY_METHOD_PREFIX);
        StringBuilder getPropertyCode = new StringBuilder(CODE_GET_PROPERTY_METHOD_PREFIX);
        StringBuilder invokeMethodCode = new StringBuilder(CODE_INVOKE_METHOD_PREFIX);

        setPropertyCode.append(String.format(CODE_GET_TARGET_OBJECT, clazzName, clazzName));
        getPropertyCode.append(String.format(CODE_GET_TARGET_OBJECT, clazzName, clazzName));
        invokeMethodCode.append(String.format(CODE_GET_TARGET_OBJECT, clazzName, clazzName));

        Map<String, Class<?>> propertyMap = new HashMap<>(); // <property name, property types>
        Map<String, Method> methodMap = new LinkedHashMap<>(); // <method desc, Method instance>
        List<String> methodNames = new ArrayList<>(); // method names.
        List<String> declaredMethodNames = new ArrayList<>(); // declaring method names.

        // get all public field.
        appendPublicFieldCode(c, setPropertyCode, getPropertyCode, propertyMap);

        // get all public method.
        appendPublicMethodCode(c, invokeMethodCode, methodMap, methodNames, declaredMethodNames);

        // deal with get/set method.
        appendGetterSetterCode(c, setPropertyCode, getPropertyCode, propertyMap, methodMap);

        // make class
        ClassGenerator classGenerator = makeClass(c, classLoader, setPropertyCode, getPropertyCode, invokeMethodCode, methodMap);

        try {
            Class<?> wrapperClass = classGenerator.toClass();
            // setup static field.
            wrapperClass.getField("pts").set(null, propertyMap);
            wrapperClass.getField("pns").set(null, propertyMap.keySet().toArray(new String[0]));
            wrapperClass.getField("mns").set(null, methodNames.toArray(new String[0]));
            wrapperClass.getField("dmns").set(null, declaredMethodNames.toArray(new String[0]));
            int ix = 0;
            for (Method m : methodMap.values()) {
                wrapperClass.getField("mts" + ix++).set(null, m.getParameterTypes());
            }
            return (Wrapper) wrapperClass.newInstance();
        } catch (RuntimeException e) {
            throw e;
        } catch (Throwable e) {
            throw new RuntimeException(e.getMessage(), e);
        } finally {
            classGenerator.release();
            methodMap.clear();
            methodNames.clear();
            declaredMethodNames.clear();
        }
    }

    private static ClassGenerator makeClass(Class<?> c, ClassLoader classLoader, StringBuilder setPropertyCode,
                                            StringBuilder getPropertyCode, StringBuilder invokeMethodCode,
                                            Map<String, Method> methodMap) {
        ClassGenerator classGenerator = ClassGenerator.newInstance(classLoader);
        long id = WRAPPER_CLASS_COUNTER.getAndIncrement();
        classGenerator.setClassName((Modifier.isPublic(c.getModifiers()) ? Wrapper.class.getName() : c.getName() + "$sw") + id);
        classGenerator.setSuperClass(Wrapper.class);

        classGenerator.addDefaultConstructor();
        classGenerator.addField("public static String[] pns;"); // property name array.
        classGenerator.addField("public static java.util.Map pts;"); // property type map. <property name, property types>
        classGenerator.addField("public static String[] mns;"); // all method name array.
        classGenerator.addField("public static String[] dmns;"); // declared method name array.
        for (int i = 0, len = methodMap.size(); i < len; i++) {
            classGenerator.addField("public static Class[] mts" + i + ";");
        }

        classGenerator.addMethod("public String[] getPropertyNames(){ return pns; }");
        classGenerator.addMethod("public boolean hasProperty(String n){ return pts.containsKey($1); }");
        classGenerator.addMethod("public Class getPropertyType(String n){ return (Class)pts.get($1); }");
        classGenerator.addMethod("public String[] getMethodNames(){ return mns; }");
        classGenerator.addMethod("public String[] getDeclaredMethodNames(){ return dmns; }");
        classGenerator.addMethod(setPropertyCode.toString());
        classGenerator.addMethod(getPropertyCode.toString());
        classGenerator.addMethod(invokeMethodCode.toString());
        return classGenerator;
    }

    private static void appendGetterSetterCode(Class<?> c, StringBuilder setPropertyCode, StringBuilder getPropertyCode,
                                               Map<String, Class<?>> propertyMap, Map<String, Method> methodMap) {
        Matcher matcher;
        for (Map.Entry<String, Method> entry : methodMap.entrySet()) {
            String methodDesc = entry.getKey();
            Method method = entry.getValue();
            if ((matcher = ReflectUtils.GETTER_METHOD_DESC_PATTERN.matcher(methodDesc)).matches()) {
                // method starts with get
                String pn = propertyName(matcher.group(1));
                getPropertyCode.append(String.format(CODE_GETTER, pn, method.getName()));
                propertyMap.put(pn, method.getReturnType());
            } else if ((matcher = ReflectUtils.IS_HAS_CAN_METHOD_DESC_PATTERN.matcher(methodDesc)).matches()) {
                // method starts with is/has/can
                String pn = propertyName(matcher.group(1));
                getPropertyCode.append(String.format(CODE_GETTER, pn, method.getName()));
                propertyMap.put(pn, method.getReturnType());
            } else if ((matcher = ReflectUtils.SETTER_METHOD_DESC_PATTERN.matcher(methodDesc)).matches()) {
                // method starts with set
                Class<?> pt = method.getParameterTypes()[0];
                String pn = propertyName(matcher.group(1));
                setPropertyCode.append(String.format(CODE_SETTER, pn, method.getName(), arg(pt, "$3")));
                propertyMap.put(pn, pt);
            }
        }
        setPropertyCode.append(String.format(CODE_THROW_NO_SUCH_METHOD, c.getName()));
        getPropertyCode.append(String.format(CODE_THROW_NO_SUCH_METHOD, c.getName()));
    }

    private static void appendPublicMethodCode(Class<?> c, StringBuilder invokeMethodCode, Map<String, Method> methodMap,
                                               List<String> methodNames, List<String> declaredMethodNames) {
        Method[] methods = c.getMethods();
        boolean hasMethod = hasMethods(methods);
        if (hasMethod) {
            invokeMethodCode.append(CODE_TRY_METHOD_PREFIX);
            for (Method method : methods) {
                //ignore Object's method.
                if (method.getDeclaringClass() == Object.class) {
                    continue;
                }

                // choose which method is invoked
                String methodName = method.getName();
                int len = method.getParameterTypes().length;
                invokeMethodCode.append(String.format(CODE_CHECK_PARAM, methodName, len));

                // if the method has override methods, check each parameter
                boolean override = false;
                for (Method m2 : methods) {
                    if (method != m2 && method.getName().equals(m2.getName())) {
                        override = true;
                        break;
                    }
                }
                if (override) {
                    for (int l = 0; l < len; l++) {
                        invokeMethodCode.append(String.format(CODE_CHECK_OVERRIDE, l, method.getParameterTypes()[l].getName()));
                    }
                }
                invokeMethodCode.append(CODE_END_CHECK);

                // invoke method
                if (method.getReturnType() == Void.TYPE) {
                    invokeMethodCode.append(String.format(CODE_INVOKE_VOID_RETURN, methodName, args(method.getParameterTypes(), "$4")));
                } else {
                    invokeMethodCode.append(String.format(CODE_INVOKE_OBJECT_RETURN, methodName, args(method.getParameterTypes(), "$4")));
                }

                methodNames.add(methodName);
                if (method.getDeclaringClass() == c) {
                    declaredMethodNames.add(methodName);
                }
                methodMap.put(ReflectUtils.getDesc(method), method);
            }
            invokeMethodCode.append(CODE_TRY_METHOD_SUFFIX);
        }
        invokeMethodCode.append(String.format(CODE_THROW_NO_SUCH_METHOD, c.getName()));
    }

    private static void appendPublicFieldCode(Class<?> c, StringBuilder setPropertyCode,
                                              StringBuilder getPropertyCode, Map<String, Class<?>> propertyMap) {
        for (Field field : c.getFields()) {
            String fieldName = field.getName();
            Class<?> fieldType = field.getType();
            if (Modifier.isStatic(field.getModifiers()) || Modifier.isTransient(field.getModifiers())) {
                continue;
            }

            setPropertyCode.append(String.format(CODE_SET_FIELD, fieldName, fieldName, arg(fieldType, "$3")));
            getPropertyCode.append(String.format(CODE_GET_FIELD, fieldName, fieldName));
            propertyMap.put(fieldName, fieldType);
        }
    }

    private static String arg(Class<?> cl, String name) {
        if (cl.isPrimitive()) {
            if (cl == Boolean.TYPE) {
                return "((Boolean)" + name + ").booleanValue()";
            }
            if (cl == Byte.TYPE) {
                return "((Byte)" + name + ").byteValue()";
            }
            if (cl == Character.TYPE) {
                return "((Character)" + name + ").charValue()";
            }
            if (cl == Double.TYPE) {
                return "((Number)" + name + ").doubleValue()";
            }
            if (cl == Float.TYPE) {
                return "((Number)" + name + ").floatValue()";
            }
            if (cl == Integer.TYPE) {
                return "((Number)" + name + ").intValue()";
            }
            if (cl == Long.TYPE) {
                return "((Number)" + name + ").longValue()";
            }
            if (cl == Short.TYPE) {
                return "((Number)" + name + ").shortValue()";
            }
            throw new RuntimeException("Unknown primitive type: " + cl.getName());
        }
        return "(" + ReflectUtils.getName(cl) + ")" + name;
    }

    private static String args(Class<?>[] cs, String name) {
        int len = cs.length;
        if (len == 0) {
            return "";
        }
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < len; i++) {
            if (i > 0) {
                sb.append(',');
            }
            sb.append(arg(cs[i], name + "[" + i + "]"));
        }
        return sb.toString();
    }

    private static String propertyName(String pn) {
        return pn.length() == 1 || Character.isLowerCase(pn.charAt(1)) ? Character.toLowerCase(pn.charAt(0)) + pn.substring(1) : pn;
    }

    private static boolean hasMethods(Method[] methods) {
        if (methods == null || methods.length == 0) {
            return false;
        }
        for (Method m : methods) {
            if (m.getDeclaringClass() != Object.class) {
                return true;
            }
        }
        return false;
    }

    /**
     * get property name array.
     *
     * @return property name array.
     */
    abstract public String[] getPropertyNames();

    /**
     * get property type.
     *
     * @param pn property name.
     * @return Property type or nul.
     */
    abstract public Class<?> getPropertyType(String pn);

    /**
     * has property.
     *
     * @param name property name.
     * @return has or has not.
     */
    abstract public boolean hasProperty(String name);

    /**
     * get property value.
     *
     * @param instance instance.
     * @param pn       property name.
     * @return value.
     */
    abstract public Object getPropertyValue(Object instance, String pn) throws NoSuchPropertyException, IllegalArgumentException;

    /**
     * set property value.
     *
     * @param instance instance.
     * @param pn       property name.
     * @param pv       property value.
     */
    abstract public void setPropertyValue(Object instance, String pn, Object pv) throws NoSuchPropertyException, IllegalArgumentException;

    /**
     * get property value.
     *
     * @param instance instance.
     * @param pns      property name array.
     * @return value array.
     */
    public Object[] getPropertyValues(Object instance, String[] pns) throws NoSuchPropertyException, IllegalArgumentException {
        Object[] ret = new Object[pns.length];
        for (int i = 0; i < ret.length; i++) {
            ret[i] = getPropertyValue(instance, pns[i]);
        }
        return ret;
    }

    /**
     * set property value.
     *
     * @param instance instance.
     * @param pns      property name array.
     * @param pvs      property value array.
     */
    public void setPropertyValues(Object instance, String[] pns, Object[] pvs) throws NoSuchPropertyException, IllegalArgumentException {
        if (pns.length != pvs.length) {
            throw new IllegalArgumentException("pns.length != pvs.length");
        }

        for (int i = 0; i < pns.length; i++) {
            setPropertyValue(instance, pns[i], pvs[i]);
        }
    }

    /**
     * get method name array.
     *
     * @return method name array.
     */
    abstract public String[] getMethodNames();

    /**
     * get method name array.
     *
     * @return method name array.
     */
    abstract public String[] getDeclaredMethodNames();

    /**
     * has method.
     *
     * @param name method name.
     * @return has or has not.
     */
    public boolean hasMethod(String name) {
        for (String mn : getMethodNames()) {
            if (mn.equals(name)) {
                return true;
            }
        }
        return false;
    }

    /**
     * invoke method.
     *
     * @param instance instance.
     * @param mn       method name.
     * @param types
     * @param args     argument array.
     * @return return value.
     */
    abstract public Object invokeMethod(Object instance, String mn, Class<?>[] types, Object[] args) throws NoSuchMethodException, InvocationTargetException;
}
