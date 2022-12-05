package org.apache.dubbo.rpc.protocol.rest.netty4;

import org.apache.dubbo.common.URL;
import org.apache.dubbo.rpc.Invoker;
import org.apache.dubbo.rpc.RpcInvocation;
import org.apache.dubbo.rpc.model.MethodDescriptor;
import org.apache.dubbo.rpc.model.ServiceModel;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class RestResolver {
    private final RestPathResolver restPathResolver;

    public RestResolver() {
        this.restPathResolver = new RestPathResolver();
    }

    public void add(String path, Invoker<?> invoker) {
        restPathResolver.add(path, invoker);
    }

    public RpcInvocation resolve(String uri, String method, Iterable<Map.Entry<String, String>> headers) {
        URL url = URL.valueOf(uri);
        String[] requests = url.getPath().split("/");

        Invoker<?> invoker = restPathResolver.resolve(requests[0], method, url.getGroup(), url.getVersion());
        if (invoker == null) {
            return null;
        }
        //        String targetServiceUniqueName, ServiceModel serviceModel, String methodName, String interfaceName, String protocolServiceKey, Class<?>[] parameterTypes, Object[] arguments,
        //                         Map<String, Object> attachments, Invoker<?> invoker, Map<Object, Object> attributes, InvokeMode invokeMode
        ServiceModel serviceModel = invoker.getUrl().getServiceModel();
        String methodName = requests[1];
        String interfaceName = serviceModel.getServiceInterfaceClass().getName();
        String protocolServiceKey = "rest/" + serviceModel.getServiceKey();
        List<MethodDescriptor> methods = serviceModel.getServiceModel().getMethods(methodName);
        if (methods == null || methods.isEmpty()) {
            return null;
        }
        MethodDescriptor methodDescriptor = methods.get(0);
        Class<?>[] parameterTypes = methodDescriptor.getParameterClasses();
        Object[] arguments = new Object[parameterTypes.length];
        Map<String, Object> attachments = new HashMap<>();
        headers.forEach(entry -> attachments.put(entry.getKey(), entry.getValue()));
        return new RpcInvocation(
            serviceModel.getServiceKey(),
            serviceModel,
            methodName,
            interfaceName,
            protocolServiceKey,
            parameterTypes,
            arguments, attachments, invoker, null, null);
    }

    public RpcInvocation fillHeaders(RpcInvocation rpcInvocation, Iterable<Map.Entry<String, String>> headers) {
        headers.forEach(entry -> rpcInvocation.setAttachment(entry.getKey(), entry.getValue()));
        return rpcInvocation;
    }

    public RpcInvocation fillBody(RpcInvocation rpcInvocation, String body) {
        return rpcInvocation;
    }
}
